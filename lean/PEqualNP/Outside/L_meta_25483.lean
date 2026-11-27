import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25483_aux

namespace GateBridge

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (FanInTwo)
open PEqualNP.MetaComplexity.NestedCover (ReadsBack gateAt)

variable {α : Type*}

private def Scheduled (n : ℕ) (F : α → (Fin n → Bool) → Bool) (k : ℕ) (S : Set α) : Prop :=
  ∃ gs : List Gate, gs.length = k ∧ ReadsBack n ⟨gs, 0⟩ ∧ FanInTwo ⟨gs, 0⟩ ∧
    ∀ a ∈ S, ∃ i : ℕ, i < n + k ∧
      ∀ x : Fin n → Bool, ((Circuit.mk gs 0).wires (List.ofFn x)).getD i false = F a x

private theorem wireLength (C : Circuit) (w : List Bool) :
    (C.wires w).length = w.length + C.gates.length := by
  rcases C with ⟨gs, out⟩
  change (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    w).length = w.length + gs.length
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

private theorem start {n : ℕ} {F : α → (Fin n → Bool) → Bool}
    (input : Fin n → α) (h : ∀ i x, F (input i) x = x i) :
    Scheduled n F 0 (Set.range input) := by
  refine ⟨[], rfl, ?_, ?_, ?_⟩
  · simp [ReadsBack]
  · simp [FanInTwo]
  · intro a ha
    obtain ⟨i, rfl⟩ := Set.mem_range.mp ha
    refine ⟨i.val, by simpa using i.isLt, fun x => ?_⟩
    change (List.ofFn x).getD i.val false = F (input i) x
    rw [List.getD_eq_getElem _ _ (by simpa using i.isLt), List.getElem_ofFn, h i x]

private theorem restrict {n k : ℕ} {F : α → (Fin n → Bool) → Bool} {S T : Set α}
    (h : Scheduled n F k S) (hsub : T ⊆ S) : Scheduled n F k T := by
  obtain ⟨gs, hs, hr, hf, hw⟩ := h
  exact ⟨gs, hs, hr, hf, fun a ha => hw a (hsub ha)⟩

private theorem realizeDeps {n k : ℕ} {F : α → (Fin n → Bool) → Bool} {S : Set α}
    {gs : List Gate}
    (hw : ∀ a ∈ S, ∃ i : ℕ, i < n + k ∧
      ∀ x : Fin n → Bool, ((Circuit.mk gs 0).wires (List.ofFn x)).getD i false = F a x)
    (deps : List α) (hdeps : ∀ a ∈ deps, a ∈ S) :
    ∃ is : List ℕ, is.length = deps.length ∧ (∀ i ∈ is, i < n + k) ∧
      ∀ x : Fin n → Bool,
        is.map (fun i => ((Circuit.mk gs 0).wires (List.ofFn x)).getD i false) =
          deps.map (fun a => F a x) := by
  induction deps with
  | nil => exact ⟨[], rfl, by simp, by simp⟩
  | cons a deps ih =>
    obtain ⟨i, hi, hval⟩ := hw a (hdeps a List.mem_cons_self)
    obtain ⟨is, hlen, hbound, hvals⟩ := ih (fun b hb => hdeps b (List.mem_cons_of_mem a hb))
    refine ⟨i :: is, by simp [hlen], ?_, fun x => ?_⟩
    · intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · exact hi
      · exact hbound j hj
    · simp only [List.map_cons, hval x, hvals x]

private theorem push {n k : ℕ} {F : α → (Fin n → Bool) → Bool} {S : Set α}
    (h : Scheduled n F k S) (op : GateOp) (deps : List α) (out : α)
    (hop : op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hlen : deps.length ≤ 2) (hdeps : ∀ a ∈ deps, a ∈ S)
    (hval : ∀ x, F out x = op.eval (deps.map fun a => F a x)) :
    Scheduled n F (k + 1) (insert out S) := by
  obtain ⟨gs, hgs, hr, hf, hw⟩ := h
  obtain ⟨is, his, hbound, hvalues⟩ := realizeDeps hw deps hdeps
  let g : Gate := ⟨op, is⟩
  have hlength (x : Fin n → Bool) :
      ((Circuit.mk gs 0).wires (List.ofFn x)).length = n + k := by
    rw [wireLength]
    simpa using congrArg (n + ·) hgs
  have hsnoc (x : Fin n → Bool) :
      (Circuit.mk (gs ++ [g]) 0).wires (List.ofFn x) =
        (Circuit.mk gs 0).wires (List.ofFn x) ++ [F out x] := by
    simp only [Circuit.wires, List.foldl_append, List.foldl_cons, List.foldl_nil]
    change (Circuit.mk gs 0).wires (List.ofFn x) ++
      [op.eval (is.map fun i => ((Circuit.mk gs 0).wires (List.ofFn x)).getD i false)] =
        (Circuit.mk gs 0).wires (List.ofFn x) ++ [F out x]
    rw [hvalues x, hval x]
  refine ⟨gs ++ [g], by simp [hgs], ?_, ?_, ?_⟩
  · intro j hj i hi
    change j < (gs ++ [g]).length at hj
    change i ∈ ((gs ++ [g]).getD j ⟨GateOp.or, []⟩).inputs at hi
    by_cases hj' : j < gs.length
    · rw [List.getD_append _ _ _ _ hj'] at hi
      exact hr j hj' i hi
    · have heq : j = gs.length := by
        simp only [List.length_append, List.length_singleton] at hj
        omega
      subst j
      rw [List.getD_append_right _ _ _ _ le_rfl] at hi
      have hi' : i ∈ is := by simpa [g] using hi
      simpa [hgs] using hbound i hi'
  · intro g' hg'
    change g' ∈ gs ++ [g] at hg'
    rcases List.mem_append.mp hg' with hg' | hg'
    · exact hf g' hg'
    · have heq : g' = g := List.mem_singleton.mp hg'
      subst g'
      refine ⟨hop, ?_⟩
      change is.length ≤ 2
      simpa only [his] using hlen
  · intro a ha
    rcases Set.mem_insert_iff.mp ha with rfl | ha
    · refine ⟨n + k, by omega, fun x => ?_⟩
      rw [hsnoc x, List.getD_append_right _ _ _ _ (by simp [hlength x])]
      simp [hlength x]
    · obtain ⟨i, hi, hval'⟩ := hw a ha
      refine ⟨i, by omega, fun x => ?_⟩
      rw [hsnoc x, List.getD_append _ _ _ _ (by simpa [hlength x] using hi), hval' x]

private theorem finish {n k : ℕ} {F : α → (Fin n → Bool) → Bool} {S : Set α} {out : α}
    (h : Scheduled n F k S) (hout : out ∈ S) :
    ∃ C : Circuit, C.size = k ∧ ReadsBack n C ∧ FanInTwo C ∧
      ∀ x : Fin n → Bool, C.eval (List.ofFn x) = F out x := by
  obtain ⟨gs, hgs, hr, hf, hw⟩ := h
  obtain ⟨i, _, hi⟩ := hw out hout
  exact ⟨⟨gs, i⟩, hgs, hr, hf, hi⟩

end GateBridge

namespace Sweep25483

private def mix2 (x : Nat → Bool) (n : Nat) : Bool :=
  xor (xor (x n) (x (n + 2))) (x (n + 4))

private def core2 (x : Nat → Bool) (n : Nat) : Bool :=
  xor (mix2 x n) (!(mix2 x (n + 1)) && mix2 x (n + 2))

private theorem core2_congr {x y : Nat → Bool} {n : Nat}
    (H : ∀ i, n ≤ i → i ≤ n + 6 → x i = y i) : core2 x n = core2 y n := by
  unfold core2 mix2
  rw [H n (by omega) (by omega), H (n + 1) (by omega) (by omega),
    H (n + 2) (by omega) (by omega), H (n + 3) (by omega) (by omega),
    H (n + 4) (by omega) (by omega), H (n + 5) (by omega) (by omega),
    H (n + 6) (by omega) (by omega)]

private def col (v : Nat → Bool) (c : Nat → Nat → Bool)
    (x : Nat → Bool) : Nat → Nat → Bool
  | 0, n => x (n + 1)
  | t + 1, n => xor (xor (core2 (col v c x t) n)
     (xor (x (n + (3 - (t + 1)))) (v (n + (3 - (t + 1)))))) (c (t + 1) n)

private theorem col_congr {v c x y} {t n : Nat} (ht : t < 3)
    (H : ∀ i, n + 1 ≤ i → i ≤ n + 1 + 6 * t → x i = y i) :
    col v c x t n = col v c y t n := by
  induction t generalizing n with
  | zero => simp only [col]; apply H <;> omega
  | succ t IH =>
    simp only [col]
    rw [H (n + (3 - (t + 1))) (by omega) (by omega)]
    congr 2
    apply core2_congr
    intro i hi hj
    apply IH (by omega)
    intro j hj₁ hj₂
    apply H j <;> omega

private def pivot2 (v : Nat → Bool) (c : Nat → Nat → Bool)
    (x : Nat → Bool) (n : Nat) : Bool :=
  xor (xor (core2 (col v c x 2) n) (v n)) (c 3 n)

private theorem pivot2_congr {v c x y n}
    (H : ∀ i, n + 1 ≤ i → i ≤ n + 19 → x i = y i) :
    pivot2 v c x n = pivot2 v c y n := by
  unfold pivot2
  congr 2
  apply core2_congr
  intro i hi hj
  apply col_congr (by omega)
  intro j hj₁ hj₂
  apply H j <;> omega

private theorem col_zero_iff {v c x n} :
    col v c x 3 n = false ↔ x n = pivot2 v c x n := by
  have heq : col v c x 3 n = xor (xor (core2 (col v c x 2) n)
      (xor (x n) (v n))) (c 3 n) := by
    simp only [col, Nat.sub_self, Nat.add_zero]
  rw [heq]
  unfold pivot2
  cases x n <;> cases v n <;> cases c 3 n <;>
    cases core2 (col v c x 2) n <;> decide

private def fill (v : Nat → Bool) (c : Nat → Nat → Bool) :
    Nat → (Nat → Bool) → (Nat → Bool)
  | 0, x => x
  | n + 1, x => fill v c n (Function.update x n (pivot2 v c x n))

private theorem fill_ge {v c q x i} (H : q ≤ i) : fill v c q x i = x i := by
  induction q generalizing x with
  | zero => rfl
  | succ q IH =>
    rw [fill, IH (by omega)]
    exact Function.update_of_ne (by omega) _ _

private theorem fill_lt {v c q x i} (H : i < q) :
    fill v c q x i = pivot2 v c (fill v c q x) i := by
  induction q generalizing x with
  | zero => omega
  | succ q IH =>
    rw [fill]
    by_cases h : i < q
    · exact IH h
    · obtain rfl : i = q := by omega
      rw [fill_ge (by omega), Function.update_self]
      apply pivot2_congr
      intro j hj _
      rw [fill_ge (by omega), Function.update_of_ne (by omega)]

private theorem fill_unique {v c q k x y} (hq : q + 19 ≤ k)
    (hseed : ∀ i, q ≤ i → i < k → x i = y i)
    (hx : ∀ i < q, x i = pivot2 v c x i)
    (hy : ∀ i < q, y i = pivot2 v c y i) :
    ∀ i < k, x i = y i := by
  let P := fun d : Nat => ∀ i < k, k - i = d → x i = y i
  have all (d : Nat) : P d := by
    induction d using Nat.strong_induction_on with
    | ind d IH =>
      intro i hik hid
      by_cases h : q ≤ i
      · exact hseed i h hik
      · rw [hx i (by omega), hy i (by omega)]
        apply pivot2_congr
        intro j hj₁ hj₂
        exact IH (k - j) (by omega) j (by omega) rfl
  exact fun i hi => all (k - i) i hi rfl

end Sweep25483

namespace BitBridge

private def stepBit (k word i : Nat) : Bool :=
  word.testBit i ^^ (!(word.testBit ((i + 1) % k)) && word.testBit ((i + 2) % k))

private def wordStep (k word : Nat) : Nat :=
  (List.range k).foldl (fun acc i => if stepBit k word i then acc ||| 2 ^ i else acc) 0

private theorem testBit_foldl_set (p : Nat → Bool) (xs : List Nat) (acc i : Nat) :
    (xs.foldl (fun a j => if p j then a ||| 2 ^ j else a) acc).testBit i =
      (acc.testBit i || (decide (i ∈ xs) && p i)) := by
  induction xs generalizing acc with
  | nil => simp
  | cons j xs ih =>
    simp only [List.foldl_cons, ih]
    by_cases hji : j = i
    · subst j
      cases hp : p i <;> simp [hp]
    · cases hp : p j <;> simp [hp, Nat.testBit_two_pow, hji, Ne.symm hji]

private theorem testBit_wordStep_all (k word i : Nat) :
    (wordStep k word).testBit i = (decide (i < k) && stepBit k word i) := by
  simp only [wordStep, testBit_foldl_set, Nat.zero_testBit, Bool.false_or, List.mem_range]

private theorem testBit_wordStep {k word i : Nat} (hi : i < k) :
    (wordStep k word).testBit i =
      (word.testBit i ^^ (!(word.testBit ((i + 1) % k)) && word.testBit ((i + 2) % k))) := by
  simp [testBit_wordStep_all, stepBit, hi]

private theorem wordStep_lt (k word : Nat) : wordStep k word < 2 ^ k := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  simp [testBit_wordStep_all, Nat.not_lt_of_ge hi]

private theorem lt_two_pow_iff_testBit {n k a : Nat} (hn : n < 2 ^ k) :
    n < 2 ^ a ↔ ∀ i, a ≤ i → i < k → n.testBit i = false := by
  constructor
  · intro ha i hai _
    exact Nat.testBit_lt_two_pow (ha.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two hai))
  · intro h
    apply Nat.lt_pow_two_of_testBit
    intro i hai
    by_cases hi : i < k
    · exact h i hai hi
    · exact Nat.testBit_lt_two_pow
        (hn.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two (Nat.le_of_not_gt hi)))

private def rot (k s w : Nat) : Nat :=
  ((w <<< (s % k)) ||| (w >>> (k - s % k))) % 2 ^ k

private theorem rot_lt {k s w : Nat} : rot k s w < 2 ^ k :=
  Nat.mod_lt _ (Nat.two_pow_pos _)

private theorem bit_rot {k s w i : Nat} (wlt : w < 2 ^ k) (ilt : i < k) :
    (rot k s w).testBit i = w.testBit ((i + k - s % k) % k) := by
  have hs : s % k < k := Nat.mod_lt _ (by omega)
  simp only [rot, Nat.testBit_mod_two_pow, ilt, decide_true, Bool.true_and,
    Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  by_cases h : s % k ≤ i
  · have hz : w.testBit (k - s % k + i) = false :=
      Nat.testBit_lt_two_pow (wlt.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two (by omega)))
    have he : (i + k - s % k) % k = i - s % k := by
      rw [Nat.mod_eq_sub_mod (by omega : k ≤ i + k - s % k), Nat.mod_eq_of_lt (by omega)]
      omega
    simp [h, hz, he]
  · have he : (i + k - s % k) % k = k - s % k + i := by
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    simp [h, he]

private theorem lt_xor {a b k : Nat} (ha : a < 2 ^ k) (hb : b < 2 ^ k) :
    a ^^^ b < 2 ^ k := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  have hm := Nat.pow_le_pow_right Nat.zero_lt_two hi
  simp [Nat.testBit_xor, Nat.testBit_lt_two_pow (ha.trans_le hm),
    Nat.testBit_lt_two_pow (hb.trans_le hm)]

private theorem wordStep_eq (k word : Nat) :
    wordStep k word = (List.range k).foldl (fun acc i =>
      acc ||| ((xor (word.testBit i)
        (!(word.testBit ((i + 1) % k)) && word.testBit ((i + 2) % k))).toNat <<< i)) 0 := by
  unfold wordStep
  congr 1
  funext a j
  change (if stepBit k word j then a ||| 2 ^ j else a) =
    a ||| ((stepBit k word j).toNat <<< j)
  cases stepBit k word j <;> simp [Nat.shiftLeft_eq]

end BitBridge

namespace Word25483

open BitBridge Sweep25483
open PEqualNP.MetaComplexity (tableIndex)

private theorem pack_succ {n : Nat} (x : Fin (n + 1) → Bool) :
    tableIndex x = tableIndex (fun i : Fin n => x i.castSucc)
        + (if x (Fin.last n) = true then 2 ^ n else 0) := by
  unfold tableIndex
  rw [Fin.sum_univ_castSucc]
  rfl

private theorem pack_lt : ∀ {n : Nat} (x : Fin n → Bool), tableIndex x < 2 ^ n := by
  intro n
  induction n with
  | zero => intro x; simp [tableIndex]
  | succ n IH =>
    intro x
    rw [pack_succ, pow_succ]
    have := IH (fun i : Fin n => x i.castSucc)
    split <;> omega

private theorem bit_pack : ∀ {n : Nat} (x : Fin n → Bool) (i : Fin n),
    (tableIndex x).testBit i = x i := by
  intro n
  induction n with
  | zero => intro x i; exact i.elim0
  | succ n IH =>
    intro x i
    have hlt := pack_lt (fun i : Fin n => x i.castSucc)
    rw [pack_succ]
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [Fin.val_last]
      cases h : x (Fin.last n) <;> simp only [h, Bool.false_eq_true, ↓reduceIte]
      · rw [Nat.add_zero, Nat.testBit_lt_two_pow hlt]
      · rw [Nat.add_comm, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hlt]
        rfl
    · change (tableIndex (fun i : Fin n => x i.castSucc) +
        (if x (Fin.last n) = true then 2 ^ n else 0)).testBit j.val = x j.castSucc
      cases h : x (Fin.last n) <;> simp only [h, Bool.false_eq_true, ↓reduceIte]
      · rw [Nat.add_zero]; exact IH _ j
      · rw [Nat.add_comm, Nat.testBit_two_pow_add_gt j.isLt]; exact IH _ j

private def constant (k t : Nat) : Nat := 3 ^ (k + t) % 2 ^ k
private def updateRound (k d e t w state : Nat) : Nat :=
  wordStep k (state ^^^ rot k d state ^^^ rot k (k - d) state) ^^^ rot k e w ^^^ constant k t

private def rowWord (k w u : Nat) : Nat → Nat
  | 0 => rot k 1 w ^^^ u
  | t + 1 => updateRound k 1 (2 * t) (t + 1) w (rowWord k w u t)

private def colWord (k w v : Nat) : Nat → Nat
  | 0 => rot k 3 w ^^^ v
  | t + 1 => updateRound k 2 (3 * (t + 1) + 1) (3 + (t + 1)) w (colWord k w v t)

private theorem upd_lt (k d e t w state : Nat) : updateRound k d e t w state < 2 ^ k :=
  lt_xor (lt_xor (wordStep_lt _ _) rot_lt) (Nat.mod_lt _ (Nat.two_pow_pos _))

private theorem rowWord_lt {k w u : Nat} (hu : u < 2 ^ k) (t : Nat) : rowWord k w u t < 2 ^ k := by
  cases t
  · exact lt_xor rot_lt hu
  · exact upd_lt ..

private theorem colWord_lt {k w v : Nat} (hv : v < 2 ^ k) (t : Nat) : colWord k w v t < 2 ^ k := by
  cases t
  · exact lt_xor rot_lt hv
  · exact upd_lt ..

private theorem sub_cyclic {k a m : Nat} (hm : m ≤ k) (ha : m ≤ a) :
    (a % k + k - m) % k = (a - m) % k := by
  apply Nat.ModEq.add_right_cancel' m
  change ((a % k + k - m) + m) % k = ((a - m) + m) % k
  rw [Nat.sub_add_cancel (by omega), Nat.sub_add_cancel ha, Nat.add_mod_right, Nat.mod_mod]

private theorem rbit {k w i : Nat} (h : i < k) {m : Nat} (hm : m < k)
    (hw : w < 2 ^ k) : (rot k m w).testBit i = w.testBit ((i + k - m) % k) := by
  rw [bit_rot hw h, Nat.mod_eq_of_lt hm]

private theorem round_fold {α : Type*} (f : Nat → α) (op : α → Nat → α)
    (hf : ∀ j, f (j + 1) = op (f j) j) (t : Nat) :
    (List.range t).foldl op (f 0) = f t := by
  induction t with
  | zero => rfl
  | succ t IH => rw [List.range_succ, List.foldl_append, IH, List.foldl_cons, List.foldl_nil, hf]

private def coordBit (k z w : Nat) (i : Nat) : Bool := w.testBit ((z + i) % k)
private def coordConst3 (k z : Nat) (t i : Nat) : Bool :=
  coordBit k z (constant k (3 + t)) (i + (2 * t + 1))

private theorem colWord_norm {k z w v : Nat} (hk20 : 20 ≤ k)
    (hw : w < 2 ^ k) (hv : v < 2 ^ k) (hz : 3 ≤ z) (t : Nat) (ht : t ≤ 3) (i : Nat) :
    coordBit k z (colWord k w v t) (i + (2 * t + 1)) =
      col (coordBit k z v) (coordConst3 k z) (coordBit k z (colWord k w v 0)) t i := by
  induction t generalizing i with
  | zero => rfl
  | succ t IH =>
    let p := z + i + (2 * t + 1)
    have hk : 0 < k := by omega
    have hi : (p + 2) % k < k := Nat.mod_lt _ hk
    have e₁ : z + (i + (2 * (t + 1) + 1)) = p + 2 := by dsimp [p]; omega
    have hlin (j : Nat) :
        (colWord k w v t ^^^ rot k 2 (colWord k w v t) ^^^
          rot k (k - 2) (colWord k w v t)).testBit ((p + j + 2) % k) =
        Sweep25483.mix2 (col (coordBit k z v) (coordConst3 k z)
          (coordBit k z (colWord k w v 0)) t) (i + j) := by
      have hm := Nat.mod_lt (p + j + 2) hk
      have hs : ((p + j + 2) % k + k - 2) % k = (p + j) % k := by
        rw [sub_cyclic (by omega) (by omega)]
        simp
      have hs' : ((p + j + 2) % k + k - (k - 2)) % k = (p + j + 4) % k := by
        rw [show (p + j + 2) % k + k - (k - 2) = (p + j + 2) % k + 2 by omega, Nat.mod_add_mod]
      rw [Nat.testBit_xor, Nat.testBit_xor, rbit hm (by omega) (colWord_lt hv t),
        rbit hm (by omega) (colWord_lt hv t), hs, hs']
      have H (d : Nat) := IH (by omega) (i + j + d)
      simp only [coordBit] at H
      have he (d : Nat) : z + (i + j + d + (2 * t + 1)) = p + j + d := by dsimp [p]; omega
      simp only [he] at H
      rw [show (p + j) % k = (p + j + 0) % k by rfl, H 0, H 2, H 4]
      simp [Sweep25483.mix2, Bool.xor_comm, Nat.add_assoc]
    have hkey :
        (rot k (3 * (t + 1) + 1) w).testBit ((p + 2) % k) =
          xor (coordBit k z (colWord k w v 0) (i + (3 - (t + 1))))
            (coordBit k z v (i + (3 - (t + 1)))) := by
      rw [rbit hi (by omega) hw, sub_cyclic (by omega) (by dsimp [p]; omega)]
      simp only [coordBit, colWord, Nat.testBit_xor]
      rw [rbit (Nat.mod_lt _ hk) (by omega) hw,
        sub_cyclic (by omega) (by omega)]
      have he : p + 2 - (3 * (t + 1) + 1) = z + (i + (3 - (t + 1))) - 3 := by dsimp [p]; omega
      rw [he]
      cases w.testBit ((z + (i + (3 - (t + 1))) - 3) % k) <;>
        cases v.testBit ((z + (i + (3 - (t + 1)))) % k) <;> rfl
    simp only [coordBit, e₁, colWord, updateRound]
    rw [Nat.testBit_xor, Nat.testBit_xor, testBit_wordStep hi]
    rw [show ((p + 2) % k + 1) % k = (p + 1 + 2) % k by rw [Nat.mod_add_mod],
      show ((p + 2) % k + 2) % k = (p + 2 + 2) % k by rw [Nat.mod_add_mod]]
    rw [show (p + 2) % k = (p + 0 + 2) % k by rfl, hlin 0, hlin 1, hlin 2]
    simp only [Nat.add_zero]
    rw [hkey]
    simp only [col, core2, coordConst3, coordBit, e₁, colWord]

end Word25483

namespace Build25483

open PEqualNP.CircuitLowerBounds

variable {n : Nat}
private abbrev Sig (n : Nat) := (Fin n → Bool) → Bool
private def Build (A B : Set (Sig n)) (b : Nat) : Prop :=
  True ∧ (∀ {m S}, GateBridge.Scheduled n id m S → A ⊆ S →
    ∃ c ≤ b, GateBridge.Scheduled n id (m + c) (S ∪ B))

private theorem Build.run {A B : Set (Sig n)} {b m S} (H : Build A B b)
    (HS : GateBridge.Scheduled n id m S) (hA : A ⊆ S) :
    ∃ c ≤ b, GateBridge.Scheduled n id (m + c) (S ∪ B) := H.2 HS hA

private theorem idle {A B : Set (Sig n)} (h : B ⊆ A) : Build A B 0 := by
  refine ⟨trivial, ?_⟩
  intro m S HS hA
  refine ⟨0, Nat.le_refl _, ?_⟩
  simpa [Set.union_eq_left.mpr (h.trans hA)] using HS

private theorem relax {A B C D : Set (Sig n)} {b d : Nat}
    (H : Build A B b) (hA : A ⊆ C) (hB : D ⊆ B) (h : b ≤ d) : Build C D d := by
  refine ⟨trivial, ?_⟩
  intro m S HS hC
  obtain ⟨c, hc, HS'⟩ := H.run HS (hA.trans hC)
  exact ⟨c, hc.trans h, GateBridge.restrict HS' (Set.union_subset_union le_rfl hB)⟩

private theorem seq {A B C : Set (Sig n)} {b c : Nat}
    (H : Build A B b) (J : Build (A ∪ B) C c) : Build A (B ∪ C) (b + c) := by
  refine ⟨trivial, ?_⟩
  intro m S HS hA
  obtain ⟨d, hd, K⟩ := H.run HS hA
  obtain ⟨e, he, K'⟩ := J.run K (Set.union_subset_union hA le_rfl)
  exact ⟨d + e, Nat.add_le_add hd he, by simpa [Nat.add_assoc, Set.union_assoc] using K'⟩

private theorem one {A : Set (Sig n)} (op : GateOp) (deps : List (Sig n))
    (hop : op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) (hlen : deps.length ≤ 2)
    (hd : ∀ g ∈ deps, g ∈ A) (f : Sig n)
    (hv : ∀ x, f x = op.eval (deps.map fun g => g x)) : Build A {f} 1 := by
  refine ⟨trivial, ?_⟩
  intro m S HS hA
  refine ⟨1, le_rfl, ?_⟩
  have h := GateBridge.push HS op deps f hop hlen (fun g hg => hA (hd g hg)) hv
  rw [Set.insert_eq] at h
  exact GateBridge.restrict h (by intro g hg; exact hg.elim Or.inr Or.inl)

private def an (f g : Sig n) : Sig n := fun x => f x && g x
private def or (f g : Sig n) : Sig n := fun x => f x || g x
private def nt (f : Sig n) : Sig n := fun x => !f x
private def xo (f g : Sig n) : Sig n := fun x => xor (f x) (g x)

private theorem andG {A : Set (Sig n)} {f g : Sig n} (hf : f ∈ A) (hg : g ∈ A) :
    Build A {an f g} 1 :=
  one .and [f, g] (by simp) (by simp) (by simpa using And.intro hf hg) _ (by simp [GateOp.eval, an])

private theorem orG {A : Set (Sig n)} {f g : Sig n} (hf : f ∈ A) (hg : g ∈ A) :
    Build A {or f g} 1 :=
  one .or [f, g] (by simp) (by simp) (by simpa using And.intro hf hg) _ (by simp [GateOp.eval, or])

private theorem notG {A : Set (Sig n)} {f : Sig n} (hf : f ∈ A) : Build A {nt f} 1 :=
  one .not [f] (by simp) (by simp) (by simpa using hf) _ (by simp [GateOp.eval, nt])

private theorem xorG {A : Set (Sig n)} {f g : Sig n} (hf : f ∈ A) (hg : g ∈ A) :
    Build A {xo f g} 4 := by
  have he : xo f g = an (or f g) (nt (an f g)) := by
    funext x
    change xor (f x) (g x) = ((f x || g x) && !(f x && g x))
    cases f x <;> cases g x <;> rfl
  rw [he]
  have h₁ := andG hf hg
  have h₂ := orG (A := A ∪ {an f g}) (Or.inl hf) (Or.inl hg)
  have h₃ := notG (A := A ∪ ({an f g} ∪ {or f g})) (f := an f g) (by simp)
  have h₄ := andG (A := A ∪ (({an f g} ∪ {or f g}) ∪ {nt (an f g)}))
    (f := or f g) (g := nt (an f g)) (by simp) (by simp)
  exact relax (seq (seq (seq h₁ h₂) h₃) h₄) le_rfl (by simp) le_rfl

private theorem constG {A : Set (Sig n)} (b : Bool) : Build A {fun _ => b} 1 := by
  cases b
  · exact one .or [] (by simp) (by simp) (by simp) _ (by intro; rfl)
  · exact one .and [] (by simp) (by simp) (by simp) _ (by intro; rfl)

private theorem mixG {A : Set (Sig n)} {f g h : Sig n}
    (hf : f ∈ A) (hg : g ∈ A) (hh : h ∈ A) : Build A {xo (xo f g) h} 8 := by
  exact relax (seq (xorG hf hg)
    (xorG (A := A ∪ {xo f g}) (f := xo f g) (by simp) (Or.inl hh))) le_rfl (by simp) le_rfl

private theorem nonlinG {A : Set (Sig n)} {f g h : Sig n}
    (hf : f ∈ A) (hg : g ∈ A) (hh : h ∈ A) :
    Build A {xo f (an (nt g) h)} 6 := by
  have h₁ := notG hg
  have h₂ := andG (A := A ∪ {nt g}) (f := nt g) (by simp) (Or.inl hh)
  have h₃ := xorG (A := A ∪ ({nt g} ∪ {an (nt g) h})) (Or.inl hf)
    (g := an (nt g) h) (by simp)
  exact relax (seq (seq h₁ h₂) h₃) le_rfl (by simp) le_rfl

private theorem topological {α : Type*} [DecidableEq α] {A : Set (Sig n)}
    (F : α → Sig n) (rank cost : α → Nat) (s : Finset α)
    (H : ∀ i ∈ s, Build (A ∪ {f | ∃ j ∈ s, rank j < rank i ∧ f = F j}) {F i} (cost i)) :
    Build A {f | ∃ i ∈ s, f = F i} (∑ i ∈ s, cost i) := by
  classical
  induction s using Finset.strongInduction with
  | H s IH =>
    by_cases hs : s.Nonempty
    · obtain ⟨i, hi, himax⟩ := Finset.exists_max_image s rank hs
      have Hsub : s.erase i ⊂ s := Finset.erase_ssubset hi
      have hstep (j : α) (hj : j ∈ s.erase i) (l : α) (hl : l ∈ s)
          (hlt : rank l < rank j) : l ∈ s.erase i := by
        refine Finset.mem_erase.mpr ⟨?_, hl⟩
        intro heq
        subst l
        exact (Nat.not_lt_of_ge (himax j (Finset.mem_of_mem_erase hj))) hlt
      have Hs := IH (s.erase i) Hsub fun j hj =>
        relax (H j (Finset.mem_of_mem_erase hj))
          (by rintro f (hf | ⟨l, hl, hlt, rfl⟩)
              · exact Or.inl hf
              · exact Or.inr ⟨l, hstep j hj l hl hlt, hlt, rfl⟩) le_rfl le_rfl
      have Hi := relax (H i hi) (C := A ∪ {f | ∃ j ∈ s.erase i, f = F j})
        (by rintro f (hf | ⟨j, hj, hlt, rfl⟩)
            · exact Or.inl hf
            · exact Or.inr ⟨j, Finset.mem_erase.mpr ⟨by aesop, hj⟩, rfl⟩) le_rfl le_rfl
      refine relax (seq Hs Hi) le_rfl ?_ ?_
      · rintro f ⟨j, hj, rfl⟩
        by_cases he : j = i
        · exact Or.inr (by simp [he])
        · exact Or.inl ⟨j, Finset.mem_erase.mpr ⟨he, hj⟩, rfl⟩
      · rw [Finset.sum_erase_add _ _ hi]
    · have : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
      subst s
      exact relax (idle (A := A) (B := ∅) (by simp)) le_rfl (by simp) (by simp)

private theorem flipG {A : Set (Sig n)} {f : Sig n} (hf : f ∈ A) (b : Bool) :
    Build A {fun x => xor (f x) b} 1 := by
  cases b
  · have he : (fun x => xor (f x) false) = f := by funext x; cases f x <;> rfl
    rw [he]
    exact relax (idle (Set.singleton_subset_iff.mpr hf)) le_rfl le_rfl (by omega)
  · have he : (fun x => xor (f x) true) = nt f := by
      funext x
      change xor (f x) true = !f x
      cases f x <;> rfl
    rw [he]
    exact notG hf

private theorem anyG {A : Set (Sig n)} (xs : List (Sig n))
    (hs : ∀ f ∈ xs, f ∈ A) (hfalse : (fun _ => false) ∈ A) :
    Build A {fun x => xs.any (fun f => f x)} xs.length := by
  induction xs with
  | nil =>
    exact idle (Set.singleton_subset_iff.mpr hfalse)
  | cons f xs IH =>
    have H := IH (fun g hg => hs g (List.mem_cons_of_mem f hg))
    have K := orG (A := A ∪ {fun x => xs.any (fun g => g x)})
      (Or.inl (hs f List.mem_cons_self)) (Or.inr rfl)
    exact relax (seq H K) le_rfl (Set.singleton_subset_iff.mpr (Or.inr rfl)) (by simp)

private theorem allG {α : Type*} [Fintype α] {A : Set (Sig n)}
    (F : α → Sig n) (c : Nat) (H : ∀ i, Build A {F i} c) :
    Build A (Set.range F) (Fintype.card α * c) := by
  classical
  have K := topological F (fun _ => 0) (fun _ => c) Finset.univ
    (fun i _ => relax (H i) Set.subset_union_left le_rfl le_rfl)
  refine relax (by simpa only [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul] using K) le_rfl ?_ le_rfl
  rintro _ ⟨i, rfl⟩
  exact ⟨i, Finset.mem_univ _, rfl⟩

private theorem finG {k : Nat} {A : Set (Sig n)} (F : Fin k → Sig n) (c : Nat)
    (H : ∀ i, Build A {F i} c) : Build A (Set.range F) (k * c) := by
  simpa only [Fintype.card_fin] using allG F c H

private theorem notAnyG {A : Set (Sig n)} (xs : List (Sig n))
    (hs : ∀ f ∈ xs, f ∈ A) (hfalse : (fun _ => false) ∈ A) :
    Build A {fun x => !(xs.any (fun f => f x))} (xs.length + 1) :=
  relax (seq (anyG xs hs hfalse) (notG (f := fun x => xs.any (fun f => f x))
    (Or.inr rfl))) le_rfl (Set.singleton_subset_iff.mpr (Or.inr rfl)) le_rfl

end Build25483

namespace Rank25483

private def lift3 (R : Nat → Nat) (n : Nat) : Nat :=
  max (max (R n) (R (n + 1))) (R (n + 2))

private def liftM2 (R : Nat → Nat) (n : Nat) : Nat :=
  max (max (R n) (R (n + 2))) (R (n + 4))

private def cr (R : Nat → Nat) : Nat → Nat → Nat
  | 0, n => R (n + 1)
  | t + 1, n => max (lift3 (liftM2 (cr R t)) n) (R (n + (3 - (t + 1))))

private theorem lift3_le {R : Nat → Nat} {n b : Nat}
    (H : ∀ j, n ≤ j → j ≤ n + 2 → R j ≤ b) : lift3 R n ≤ b := by
  unfold lift3
  exact max_le (max_le (H _ (by omega) (by omega)) (H _ (by omega) (by omega)))
    (H _ (by omega) (by omega))

private theorem liftM2_le {R : Nat → Nat} {n b : Nat}
    (H : ∀ j, n ≤ j → j ≤ n + 4 → R j ≤ b) : liftM2 R n ≤ b := by
  unfold liftM2
  exact max_le (max_le (H _ (by omega) (by omega)) (H _ (by omega) (by omega)))
    (H _ (by omega) (by omega))

private theorem cr_le {R t n b} (ht : t < 3)
    (H : ∀ i, n + 1 ≤ i → i ≤ n + 1 + 6 * t → R i ≤ b) : cr R t n ≤ b := by
  induction t generalizing n with
  | zero => simp only [cr]; apply H <;> omega
  | succ t IH =>
    apply max_le
    · apply lift3_le
      intro i hi hi'
      apply liftM2_le
      intro j hj hj'
      apply IH (by omega)
      intro u hu hu'
      apply H u <;> omega
    · apply H <;> omega

private theorem pivotRank_le {R n b}
    (H : ∀ i, n + 1 ≤ i → i ≤ n + 19 → R i ≤ b) :
    lift3 (liftM2 (cr R 2)) n ≤ b := by
  apply lift3_le
  intro i hi hi'
  apply liftM2_le
  intro j hj hj'
  apply cr_le (by omega)
  intro u hu hu'
  apply H u <;> omega

private def point (k a h n : Nat) : Nat :=
  if a ≤ n % k ∧ n % k < h then h - n % k else 0

private theorem point_lt {k h a n j : Nat}
    (hh : h ≤ k) (ha : a ≤ n) (hn : n < h)
    (hwrap : h + 19 ≤ k + a)
    (hj : n + 1 ≤ j) (hj' : j ≤ n + 19) : point k a h j < point k a h n := by
  have hn' : point k a h n = h - n := by
    simp [point, Nat.mod_eq_of_lt (by omega : n < k), ha, hn]
  rw [hn']
  unfold point
  by_cases hjk : j < k
  · rw [Nat.mod_eq_of_lt hjk]
    split <;> omega
  · have hjmod : j % k < a := by
      rw [Nat.mod_eq_sub_mod (by omega : k ≤ j), Nat.mod_eq_of_lt (by omega : j - k < k)]
      omega
    rw [if_neg (by omega)]
    omega

private theorem mod_shift {k n i : Nat} : ((n % k) + i) % k = (n + i) % k := Nat.mod_add_mod _ _ _

private theorem cr_mod {k t : Nat} {R : Nat → Nat}
    (H : ∀ n, R (n % k) = R n) (n : Nat) : cr R t (n % k) = cr R t n := by
  have hs (A : Nat → Nat) (hA : ∀ i, A (i % k) = A i) (j l : Nat) :
      A (j % k + l) = A (j + l) := by
    rw [← hA (j % k + l), ← hA (j + l), mod_shift]
  induction t generalizing n with
  | zero => exact hs R H n _
  | succ t IH =>
    unfold cr lift3 liftM2
    simp only [IH, hs R H, hs (cr R t) IH, Nat.add_assoc]

end Rank25483

namespace ColCircuit25483

open Sweep25483 Rank25483 Build25483

private def ix {k : Nat} (hk : 0 < k) (i : Nat) : Fin k := ⟨i % k, Nat.mod_lt _ hk⟩

private theorem ix_add {k : Nat} (hk : 0 < k) (i j : Nat) :
    ix hk (i % k + j) = ix hk (i + j) := Fin.ext (Nat.mod_add_mod ..)

private theorem periodic_col {k n : Nat} (hk : 0 < k)
    (x v : Fin k → Sig n) (c : Nat → Fin k → Bool) (t i : Nat) (w : Fin n → Bool) :
    col (fun j => v (ix hk j) w) (fun j p => c j (ix hk p))
      (fun j => x (ix hk j) w) t (i % k) =
    col (fun j => v (ix hk j) w) (fun j p => c j (ix hk p))
      (fun j => x (ix hk j) w) t i := by
  let F := col (fun j => v (ix hk j) w) (fun j p => c j (ix hk p))
      (fun j => x (ix hk j) w)
  change F t (i % k) = F t i
  induction t generalizing i with
  | zero => simp [F, col, ix_add]
  | succ t IH =>
    have hperiod (j l : Nat) : F t (j % k + l) = F t (j + l) := by
      rw [← IH (j % k + l), ← IH (j + l), Nat.mod_add_mod]
    simp only [F, col, core2, Sweep25483.mix2] at *
    rw [ix_add, show ix hk (i % k) = ix hk i by exact Fin.ext (Nat.mod_mod ..)]
    simp only [Nat.add_assoc]
    rw [IH i, hperiod i 1, hperiod i 2, hperiod i 3, hperiod i 4, hperiod i 5, hperiod i 6]

private theorem pivotG {n : Nat} {A : Set (Sig n)} {a b c u : Sig n}
    (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) (hu : u ∈ A) (d : Bool) :
    Build A {fun w => xor (xor (xor (a w) (!(b w) && c w)) (u w)) d} 11 := by
  let f := xo a (an (nt b) c)
  have H₁ : Build A {f} 6 := nonlinG ha hb hc
  let g := xo f u
  have H₂ : Build (A ∪ {f}) {g} 4 := xorG (Or.inr rfl) (Or.inl hu)
  have H₃ := flipG (A := A ∪ ({f} ∪ {g})) (f := g) (by simp) d
  exact relax (seq (seq H₁ H₂) H₃) le_rfl (Set.singleton_subset_iff.mpr (Or.inr rfl)) le_rfl

private theorem colG {n : Nat} {A : Set (Sig n)} {a b c x u : Sig n}
    (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) (hx : x ∈ A) (hu : u ∈ A) (d : Bool) :
    Build A {fun w => xor (xor (xor (a w) (!(b w) && c w)) (xor (x w) (u w))) d} 15 := by
  let y := xo x u
  have H₁ : Build A {y} 4 := xorG hx hu
  have H₂ := pivotG (A := A ∪ {y}) (Or.inl ha) (Or.inl hb) (Or.inl hc) (Or.inr rfl) d
  exact relax (seq H₁ H₂) le_rfl (Set.singleton_subset_iff.mpr (Or.inr rfl)) le_rfl

private abbrev Nodes (k : Nat) := Fin k ⊕ ((Fin 3 × Fin k) ⊕ (Fin 3 × Fin k))
private def nodeCost {k : Nat} : Nodes k → Nat
  | .inl _ => 11
  | .inr (.inl _) => 8
  | .inr (.inr _) => 15

private theorem node_cost (k : Nat) :
    ∑ a : Nodes k, nodeCost a = 80 * k := by
  simp [Nodes, Fintype.sum_sum_type, nodeCost]
  ring

private theorem pr_small {k q i R : Nat} (hq : q + 19 ≤ k)
    (hi : i < q) (hR : R = q - i) : lift3 (liftM2 (cr (point k 0 q) 2)) i < R := by
  have H (j) (h1 : i + 1 ≤ j) (h2 : j ≤ i + 19) : point k 0 q j ≤ R - 1 := by
    have h := point_lt (k := k) (a := 0) (h := q) (by omega) (Nat.zero_le i) hi
      (by omega) h1 h2
    simpa [point, Nat.mod_eq_of_lt (by omega : i < k), hi, hR] using Nat.le_pred_of_lt h
  have J := pivotRank_le H
  omega

private theorem rank_add {M a b c d : Nat} (hab : a ≤ b) (hcd : c < d) :
    a * M + c < b * M + d := by
  have := Nat.mul_le_mul_right M hab
  omega

private theorem rank_next {M a b c d : Nat} (hab : a < b) (hc : c < M) :
    a * M + c < b * M + d := by
  have H := Nat.mul_le_mul_right M (Nat.succ_le_of_lt hab)
  rw [Nat.succ_mul] at H
  omega

private theorem lift3_at_le (R : Nat → Nat) (i j : Nat) (hj : j ≤ 2) : R (i + j) ≤ lift3 R i := by
  interval_cases j <;> simp [lift3, le_max_left, le_max_right] <;> omega

private theorem liftM2_at_le (R : Nat → Nat) (i d : Nat) (hd : d ≤ 2) :
    R (i + 2 * d) ≤ liftM2 R i := by
  interval_cases d <;> simp [liftM2, le_max_left, le_max_right] <;> omega

private theorem colScheduleSweep {k q n : Nat} (hk : 0 < k)
    (hq : q + 19 ≤ k) {A : Set (Sig n)} (x v : Fin k → Sig n)
    (c : Nat → Fin k → Bool) (hv : ∀ i, v i ∈ A)
    (hs : ∀ i : Fin k, q ≤ i.val → x i ∈ A)
    (hp : ∀ (i : Fin k), i.val < q → ∀ w,
      x i w = pivot2 (fun j => v (ix hk j) w) (fun t p => c t (ix hk p))
        (fun j => x (ix hk j) w) i.val) :
    Build A (Set.range x ∪ Set.range (fun i : Fin k => fun w =>
      col (fun j => v (ix hk j) w) (fun t p => c t (ix hk p))
        (fun j => x (ix hk j) w) 3 i.val)) (80 * k) := by
  let R := point k 0 q
  let B (t i : Nat) : Sig n := fun w =>
    col (fun j => v (ix hk j) w) (fun t p => c t (ix hk p)) (fun j => x (ix hk j) w) t i
  let M (t i : Nat) : Sig n := fun w =>
    Sweep25483.mix2 (fun j => B t j w) i
  let W := 8
  let F : Nodes k → Sig n
    | .inl i => x i
    | .inr (.inl (t, i)) => M t i
    | .inr (.inr (t, i)) => B (t.val + 1) i
  let rk : Nodes k → Nat
    | .inl i => R i * W
    | .inr (.inl (t, i)) => liftM2 (cr R t) i * W + (2 * t.val + 2)
    | .inr (.inr (t, i)) => cr R (t.val + 1) i * W + (2 * t.val + 3)
  have rm (i : Nat) : R (i % k) = R i := by simp [R, point]
  have bm (t i : Nat) : B t (i % k) = B t i := funext (periodic_col hk x v c t i)
  have bs (t i j : Nat) : B t (i % k + j) = B t (i + j) := by
    rw [← bm t (i % k + j), ← bm t (i + j), Nat.mod_add_mod]
  have ms (t i : Nat) : M t (i % k) = M t i := by
    unfold M Sweep25483.mix2
    simp only [bm, bs]
  have rs (t i j : Nat) : cr R t (i % k + j) = cr R t (i + j) := by
    rw [← cr_mod rm (i % k + j), ← cr_mod rm (i + j), Nat.mod_add_mod]
  have rms (t i : Nat) : liftM2 (cr R t) (i % k) = liftM2 (cr R t) i := by
    simp only [liftM2, cr_mod rm, rs]
  let Earlier (l : Nat) : Set (Sig n) := A ∪ {f | ∃ j ∈ (Finset.univ : Finset (Nodes k)), rk j < l ∧ f = F j}
  have hasX (i l : Nat) (H : R i * W < l) : x (ix hk i) ∈ Earlier l := by
    exact Or.inr ⟨.inl (ix hk i), Finset.mem_univ _, by simpa [rk, ix, rm] using H, rfl⟩
  have hasM (t : Fin 3) (i l : Nat) (H : liftM2 (cr R t) i * W + (2 * t.val + 2) < l) :
      M t i ∈ Earlier l := by
    exact Or.inr ⟨.inr (.inl (t, ix hk i)), Finset.mem_univ _,
      by simpa [rk, ix, rms] using H, (ms t i).symm⟩
  have hasB (t : Fin 3) (i l : Nat) (H : cr R (t.val + 1) i * W + (2 * t.val + 3) < l) :
      B (t.val + 1) i ∈ Earlier l := by
    exact Or.inr ⟨.inr (.inr (t, ix hk i)), Finset.mem_univ _,
      by simpa [rk, ix, cr_mod rm] using H, (bm _ _).symm⟩
  have Hb (i : Nodes k) : Build (Earlier (rk i)) {F i} (nodeCost i) := by
    rcases i with i | ⟨t, i⟩ | ⟨t, i⟩
    · by_cases hi : i.val < q
      · let j : Fin 3 := ⟨2, by omega⟩
        have rrj (d : Nat) (hd : d ≤ 2) : liftM2 (cr R j) (i.val + d) < R i := by
          have J := lift3_at_le (liftM2 (cr R j)) i d hd
          exact J.trans_lt (pr_small hq hi (by simp [R, point, Nat.mod_eq_of_lt i.isLt, hi]))
        have hm (d : Nat) (hd : d ≤ 2) : M j (i.val + d) ∈ Earlier (rk (.inl i)) := by
          apply hasM
          exact (rank_next (d := 0) (rrj d hd) (by change 2 * 2 + 2 < 8; omega))
        have H := pivotG (hm 0 (by omega)) (hm 1 (by omega)) (hm 2 (by omega))
          (Or.inl (hv (ix hk i)) : v (ix hk i) ∈ Earlier (rk (.inl i))) (c 3 (ix hk i))
        have he : x i = (fun w => pivot2 (fun j => v (ix hk j) w)
            (fun t p => c t (ix hk p)) (fun j => x (ix hk j) w) i.val) := funext (hp i hi)
        simpa only [F, nodeCost, he, pivot2, core2, M, B, Nat.add_zero] using H
      · exact relax (idle (Set.singleton_subset_iff.mpr (Or.inl (hs i (by omega)) : x i ∈ Earlier (rk (.inl i))))) le_rfl le_rfl (by simp [nodeCost])
    · have hm (d : Nat) (hd : d ≤ 2) : B t (i.val + 2 * d) ∈ Earlier (rk (.inr (.inl (t, i)))) := by
        have H := liftM2_at_le (cr R t) i d hd
        by_cases ht : t.val = 0
        · simp only [B, ht, col]
          apply hasX
          change R (i.val + 2 * d + 1) * W + 0 < liftM2 (cr R t) i * W + (2 * t.val + 2)
          exact rank_add (by simpa [ht, cr] using H) (by omega)
        · let t' : Fin 3 := ⟨t.val - 1, by omega⟩
          have et : t'.val + 1 = t.val := by dsimp [t']; omega
          rw [← et]
          apply hasB
          rw [et]
          exact rank_add H (by dsimp [t']; omega)
      have H0 : B t i.val ∈ Earlier (rk (.inr (.inl (t, i)))) := by simpa using hm 0 (by omega)
      have H1 : B t (i.val + 2) ∈ Earlier (rk (.inr (.inl (t, i)))) := by simpa using hm 1 (by omega)
      have H2 : B t (i.val + 4) ∈ Earlier (rk (.inr (.inl (t, i)))) := by simpa using hm 2 (by omega)
      exact mixG H0 H1 H2
    · have hm (d : Nat) (hd : d ≤ 2) : M t (i.val + d) ∈ Earlier (rk (.inr (.inr (t, i)))) := by
        apply hasM
        apply rank_add _ (by omega)
        exact (lift3_at_le (liftM2 (cr R t)) i d hd).trans (le_max_left ..)
      have hx : x (ix hk (i.val + (3 - (t.val + 1)))) ∈ Earlier (rk (.inr (.inr (t, i)))) := by
        apply hasX
        change R (i.val + (3 - (t.val + 1))) * W + 0 < cr R (t.val + 1) i * W + (2 * t.val + 3)
        exact rank_add (le_max_right ..) (by omega)
      exact colG (hm 0 (by omega)) (hm 1 (by omega)) (hm 2 (by omega)) hx (Or.inl (hv _)) _
  rw [← node_cost k]
  refine relax (topological F rk nodeCost Finset.univ (fun i _ => Hb i)) le_rfl ?_ le_rfl
  rintro f (⟨i, rfl⟩ | ⟨i, rfl⟩)
  · exact ⟨.inl i, Finset.mem_univ _, rfl⟩
  · let t : Fin 3 := ⟨2, by omega⟩
    refine ⟨.inr (.inr (t, i)), Finset.mem_univ _, ?_⟩
    change B 3 i = B (t.val + 1) i
    rfl

end ColCircuit25483

namespace Row25483

open BitBridge Build25483 ColCircuit25483 Word25483

private def bits {k n : Nat} (w : (Fin n → Bool) → Nat) (i : Fin k) : Sig n :=
  fun v => (w v).testBit i

private def prev {k : Nat} (hk : 0 < k) (i : Fin k) (d : Nat) : Fin k := ix hk (i.val + k - d % k)

private theorem rotG {k n : Nat} (hk : 0 < k) {A : Set (Sig n)}
    {w : (Fin n → Bool) → Nat} (hw : ∀ v, w v < 2 ^ k) (hs : ∀ i : Fin k, bits w i ∈ A)
    (d : Nat) (i : Fin k) : bits (fun v => rot k d (w v)) i ∈ A := by
  convert hs (prev hk i d) using 1
  funext v
  exact bit_rot (s := d) (hw v) i.isLt

private theorem xorBits {k n : Nat} {A : Set (Sig n)} {w u : (Fin n → Bool) → Nat} (i : Fin k)
    (hw : bits w i ∈ A) (hu : bits u i ∈ A) :
    Build A {bits (fun v => w v ^^^ u v) i} 4 := by
  have he : bits (fun v => w v ^^^ u v) i = xo (bits w i) (bits u i) := by
    funext v; exact Nat.testBit_xor ..
  rw [he]; exact xorG hw hu

private theorem rowRoundG {k n : Nat} (hk : 0 < k) {A : Set (Sig n)}
    (w s : (Fin n → Bool) → Nat) (hw : ∀ v, w v < 2 ^ k) (hs : ∀ v, s v < 2 ^ k)
    (hW : ∀ i : Fin k, bits w i ∈ A) (hS : ∀ i : Fin k, bits s i ∈ A) (e t : Nat) :
    Build A (Set.range (fun i : Fin k => bits (fun v => updateRound k 1 e t (w v) (s v)) i)) (19 * k) := by
  let w₁ := fun v => s v ^^^ rot k 1 (s v) ^^^ rot k (k - 1) (s v)
  let F := fun i : Fin k => bits w₁ i
  have H : Build A (Set.range F) (k * 8) := finG F 8 fun i => by
    have E : F i = xo (xo (bits s i) (bits (fun v => rot k 1 (s v)) i))
        (bits (fun v => rot k (k - 1) (s v)) i) := by
      funext v; simp only [F, bits, w₁, Nat.testBit_xor, xo]
    rw [E]
    exact mixG (hS i) (rotG hk hs hS 1 i) (rotG hk hs hS (k - 1) i)
  let G := fun i : Fin k => bits (fun v => updateRound k 1 e t (w v) (s v)) i
  have J : Build (A ∪ Set.range F) (Set.range G) (k * 11) := finG G 11 fun i => by
    have E : G i = (fun v => xor (xor (xor (F i v) (!(F (ix hk (i.val + 1)) v) && F (ix hk (i.val + 2)) v))
      (bits (fun v => rot k e (w v)) i v)) ((constant k t).testBit i)) := by
      funext v
      simp only [G, bits, updateRound, Nat.testBit_xor, testBit_wordStep i.isLt]
      simp only [F, bits, w₁, ix, Nat.testBit_xor]
    rw [E]
    exact pivotG (Or.inr ⟨_, rfl⟩) (Or.inr ⟨_, rfl⟩) (Or.inr ⟨_, rfl⟩)
      (Or.inl (rotG hk hw hW e i)) _
  exact relax (seq H J) le_rfl Set.subset_union_right (by omega)

private theorem rowSchedule {k n : Nat} (hk : 0 < k) {A : Set (Sig n)}
    (w u : (Fin n → Bool) → Nat) (hw : ∀ x, w x < 2 ^ k) (hu : ∀ x, u x < 2 ^ k)
    (hW : ∀ i : Fin k, bits w i ∈ A) (hU : ∀ i : Fin k, bits u i ∈ A) (t : Nat) :
    Build A (Set.range (fun i : Fin k => bits (fun x => rowWord k (w x) (u x) t) i)) (4 * k + 19 * k * t) := by
  induction t with
  | zero =>
    simpa [Nat.mul_comm] using (finG (fun i : Fin k => bits (fun x => rowWord k (w x) (u x) 0) i) 4
      (fun i => xorBits i (rotG hk hw hW 1 i) (hU i)))
  | succ t IH =>
    have H := rowRoundG hk (A := A ∪ Set.range (fun i : Fin k => bits (fun x => rowWord k (w x) (u x) t) i)) w (fun x => rowWord k (w x) (u x) t) hw
      (fun x => rowWord_lt (hu x) t) (fun i => Or.inl (hW i)) (fun i => Or.inr ⟨i, rfl⟩)
        (2 * t) (t + 1)
    exact relax (seq IH H) le_rfl Set.subset_union_right (by ring_nf; omega)

private theorem thresholds {k n : Nat} {A : Set (Sig n)} (h : Nat) (w : (Fin n → Bool) → Nat)
    (hw : ∀ v, w v < 2 ^ k) (hs : ∀ i : Fin k, h ≤ i.val → bits w i ∈ A)
    (hfalse : (fun _ => false) ∈ A) : Build A {fun v => decide (w v < 2 ^ h)} (k + 1) := by
  let xs : List (Fin k) := (List.finRange k).filter (fun i => decide (h ≤ i.val))
  have hs' : ∀ f ∈ xs.map (bits w), f ∈ A := by
    intro f hf
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hf
    exact hs i (by simpa [xs] using hi)
  have he : (fun v => !((xs.map (bits w)).any (fun f => f v))) = (fun v => decide (w v < 2 ^ h)) := by
    funext v
    apply Bool.eq_iff_iff.mpr
    rw [Bool.not_eq_true', decide_eq_true_eq, lt_two_pow_iff_testBit (hw v)]
    simp only [List.any_eq_false, List.mem_map, forall_exists_index, and_imp]
    constructor
    · intro H i hi hik
      exact Bool.eq_false_iff.mpr (H _ ⟨i, hik⟩ (by simp [xs, hi]) rfl)
    · intro H f i hi he
      subst f
      exact Bool.eq_false_iff.mp (H _ (by simpa [xs] using hi) i.isLt)
  rw [← he]
  refine relax (notAnyG _ hs' hfalse) le_rfl le_rfl (Nat.succ_le_succ ?_)
  simpa [xs] using (List.length_filter_le (p := fun i : Fin k => decide (h ≤ i.val)) (List.finRange k))

end Row25483

namespace Slot25483

open BitBridge Sweep25483 Rank25483 Word25483 Build25483 ColCircuit25483 Row25483
open PEqualNP.MetaComplexity (tableIndex)

private def inputs (n : Nat) : Set (Sig n) := Set.range (fun i : Fin n => fun v => v i)
private def base (n : Nat) : Set (Sig n) := inputs n ∪ {fun _ => false, fun _ => true}

private theorem inputG (n : Nat) : Build (inputs n) {fun _ => false, fun _ => true} 2 := by
  simpa only [Set.singleton_union] using
    (seq (constG (A := inputs n) false) (constG (A := inputs n ∪ {fun _ => false}) true))

private def U (k : Nat) (v : Fin (k + k) → Bool) : Nat := tableIndex fun i : Fin k => v (Fin.castAdd k i)
private def V (k : Nat) (v : Fin (k + k) → Bool) : Nat := tableIndex fun i : Fin k => v (Fin.natAdd k i)
private theorem U_lt (k : Nat) (v) : U k v < 2 ^ k := pack_lt _
private theorem V_lt (k : Nat) (v) : V k v < 2 ^ k := pack_lt _
private theorem bitU (k : Nat) (i : Fin k) : bits (U k) i ∈ base (k + k) := by
  exact Or.inl ⟨Fin.castAdd k i, funext fun v => (bit_pack (fun j : Fin k => v (Fin.castAdd k j)) i).symm⟩
private theorem bitV (k : Nat) (i : Fin k) : bits (V k) i ∈ base (k + k) := by
  exact Or.inl ⟨Fin.natAdd k i, funext fun v => (bit_pack (fun j : Fin k => v (Fin.natAdd k j)) i).symm⟩

private def X (k q z seed : Nat) (v : Fin (k + k) → Bool) : Nat → Bool :=
  fill (coordBit k z (V k v)) (coordConst3 k z) q (fun i => seed.testBit (i - q))

private theorem mod_inverse {k z i : Nat} (hk : 0 < k) (hi : i < k) :
    ((z + i) % k + k - z % k) % k = i := by
  have hz := Nat.mod_lt z hk
  have h := sub_cyclic (Nat.le_of_lt hz) (a := z + i) ((Nat.mod_le z k).trans (by omega))
  rw [h]
  have he : z + i - z % k = k * (z / k) + i := by
    have := Nat.mod_add_div z k
    omega
  rw [he, Nat.mul_add_mod, Nat.mod_eq_of_lt hi]

private theorem mod_inverse' {k z i : Nat} (hk : 0 < k) (hi : i < k) :
    (z + (i + k - z % k) % k) % k = i := by
  have hz := Nat.mod_lt z hk
  rw [Nat.add_mod_mod, ← Nat.mod_add_mod z k (i + k - z % k),
    show z % k + (i + k - z % k) = i + k by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hi]

private def keyBit3 {k : Nat} (z : Nat) (x : Nat → Bool) (v : Nat) (i : Fin k) : Bool :=
  let j := (i.val + 3) % k
  xor (x ((j + k - z % k) % k)) (v.testBit j)

private def key3 {k : Nat} (z : Nat) (x : Nat → Bool) (v : Nat) : Nat :=
  tableIndex (keyBit3 (k := k) z x v)

private theorem key3_coord {k z v : Nat} (hk : 3 < k) (hv : v < 2 ^ k) (x : Nat → Bool) (i : Nat) :
    coordBit k z (colWord k (key3 (k := k) z x v) v 0) i = x (i % k) := by
  have hpos : 0 < k := by omega
  let j := (z + i) % k
  have hj : j < k := Nat.mod_lt _ hpos
  let p : Fin k := ix hpos (j + k - 3)
  have he : (p.val + 3) % k = j := by
    change (((j + k - 3) % k) + 3) % k = j
    rw [Nat.mod_add_mod, Nat.sub_add_cancel (by omega), Nat.add_mod_right, Nat.mod_eq_of_lt hj]
  change (rot k 3 (key3 (k := k) z x v) ^^^ v).testBit j = _
  rw [Nat.testBit_xor, rbit hj hk (show key3 (k := k) z x v < 2 ^ k from pack_lt _)]
  change xor ((tableIndex (keyBit3 (k := k) z x v)).testBit p) (v.testBit j) = _
  rw [bit_pack]
  simp only [keyBit3, he]
  have hidx : (j + k - z % k) % k = i % k := by
    have hej : j = (z + i % k) % k := (Nat.add_mod_mod ..).symm
    rw [hej, mod_inverse hpos (Nat.mod_lt _ hpos)]
  rw [hidx]
  cases x (i % k) <;> cases v.testBit j <;> rfl

private theorem key3_unique {k z v w : Nat} (hk : 3 < k) (hv : v < 2 ^ k) (hw : w < 2 ^ k)
    {x : Nat → Bool} (H : ∀ i < k, coordBit k z (colWord k w v 0) i = x i) :
    key3 (k := k) z x v = w := by
  have hpos : 0 < k := by omega
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < k
  · let j := (i + 3) % k
    let p := (j + k - z % k) % k
    have hp : p < k := Nat.mod_lt _ hpos
    have hj : j < k := Nat.mod_lt _ hpos
    have he : (z + p) % k = j := mod_inverse' hpos hj
    have hi' : (j + k - 3) % k = i := by
      dsimp [j]
      rw [sub_cyclic (by omega) (by omega), Nat.add_sub_cancel, Nat.mod_eq_of_lt hi]
    have E := H p hp
    simp only [coordBit, he, colWord, Nat.testBit_xor, rbit hj hk hw, hi'] at E
    rw [show (key3 (k := k) z x v).testBit i = keyBit3 z x v ⟨i, hi⟩ from bit_pack _ ⟨i, hi⟩]
    change xor (x p) (v.testBit j) = w.testBit i
    rw [← E]
    cases w.testBit i <;> cases v.testBit j <;> rfl
  · have hp := Nat.pow_le_pow_right Nat.zero_lt_two (by omega : k ≤ i)
    rw [Nat.testBit_lt_two_pow ((show key3 (k := k) z x v < 2 ^ k from pack_lt _).trans_le hp),
      Nat.testBit_lt_two_pow (hw.trans_le hp)]

private theorem Xperiod_eq {k q z seed : Nat} (hq : q + 19 ≤ k)
    (w : Fin (k + k) → Bool) (i : Fin k) (hi : i.val < q) :
    X k q z seed w i = pivot2 (coordBit k z (V k w)) (coordConst3 k z)
      (fun j => X k q z seed w (j % k)) i := by
  unfold X
  rw [fill_lt hi]
  apply pivot2_congr
  intro j hj hj'
  rw [Nat.mod_eq_of_lt (by omega : j < k)]

private theorem coord_shift {k z w j : Nat} : coordBit k z w (j % k) = coordBit k z w j := by
  simp only [coordBit, Nat.add_mod_mod]

private theorem const3_shift {k z t j : Nat} :
    coordConst3 k z t (j % k) = coordConst3 k z t j := by
  unfold coordConst3 coordBit
  rw [show z + (j % k + (2 * t + 1)) = j % k + (z + (2 * t + 1)) by omega, Nat.mod_add_mod]
  congr 2
  omega

private def SKey (k q z seed : Nat) (v : Fin (k + k) → Bool) : Nat :=
  key3 (k := k) z (X k q z seed v) (V k v)

private def accept (k q z seed : Nat) (v : Fin (k + k) → Bool) : Bool :=
  decide (rowWord k (SKey k q z seed v) (U k v) 3 < 2 ^ (k - (k + 1) / 2)) &&
  decide (colWord k (SKey k q z seed v) (V k v) 3 < 2 ^ (k - (k + 1) / 2))

private theorem slotLogic {k q z seed w : Nat} (hk20 : 20 ≤ k)
    (hq : q + 19 ≤ k) (hz : 3 ≤ z) (hz' : z + 7 = k + (k - q))
    (qh : q ≤ (k + 1) / 2) (v : Fin (k + k) → Bool) (hw : w < 2 ^ k)
    (hpass : colWord k w (V k v) 3 < 2 ^ (k - (k + 1) / 2))
    (hseed : ∀ i, q ≤ i → i < k → seed.testBit (i - q) = coordBit k z (colWord k w (V k v) 0) i) :
    SKey k q z seed v = w := by
  let y := coordBit k z (colWord k w (V k v) 0)
  have hy (i : Nat) (hi : i < q) : y i = pivot2 (coordBit k z (V k v)) (coordConst3 k z) y i := by
    apply col_zero_iff.mp
    rw [← colWord_norm hk20 hw (V_lt k v) hz 3 le_rfl i]
    unfold coordBit
    have e : (z + (i + (2 * 3 + 1))) % k = i + (k - q) := by
      rw [show z + (i + (2 * 3 + 1)) = (i + (k - q)) + k by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)]
    rw [e]
    exact (lt_two_pow_iff_testBit (colWord_lt (V_lt k v) 3)).mp hpass _ (by omega) (by omega)
  have He := fill_unique hq (x := X k q z seed v) (y := y)
    (fun i hi hik => (fill_ge hi).trans (hseed i hi hik)) (fun i hi => fill_lt hi) hy
  exact key3_unique (by omega) (V_lt k v) hw (fun i hi => (He i hi).symm)

private theorem slotCircuit {k q z seed : Nat} (hk20 : 20 ≤ k)
    (hq : q + 19 ≤ k) (hz : 3 ≤ z) :
    Build (base (k + k)) {accept k q z seed} (147 * k + 3) := by
  let A := base (k + k)
  let W := SKey k q z seed
  let x : Fin k → Sig (k + k) := fun i w => X k q z seed w i
  let v : Fin k → Sig (k + k) := fun i w => coordBit k z (V k w) i
  let c : Nat → Fin k → Bool := fun t i => coordConst3 k z t i
  have hk : 0 < k := by omega
  have hx (i : Fin k) (hi : q ≤ i.val) : x i ∈ A := by
    have he : x i = (fun _ => seed.testBit (i.val - q)) := funext fun _ => fill_ge hi
    rw [he]
    cases seed.testBit (i.val - q) <;> exact Or.inr (by simp)
  have hv (i : Fin k) : v i ∈ A := bitV k (ix hk (z + i.val))
  have hp (i : Fin k) (hi : i.val < q) (w : Fin (k + k) → Bool) :
      x i w = pivot2 (fun j => v (ix hk j) w) (fun t p => c t (ix hk p))
        (fun j => x (ix hk j) w) i.val := by
    simpa only [x, v, c, ix, coord_shift, const3_shift] using Xperiod_eq hq w i hi
  let C := Set.range x ∪ Set.range (fun i : Fin k => fun w =>
    col (fun j => v (ix hk j) w) (fun t p => c t (ix hk p))
        (fun j => x (ix hk j) w) 3 i.val)
  have HC : Build A C (80 * k) := colScheduleSweep hk hq x v c hv hx hp
  let K := Set.range (fun i : Fin k => bits W i)
  have HK : Build (A ∪ C) K (k * 4) := finG _ 4 fun i => by
    let j := (i.val + 3) % k
    let p := ix hk (j + k - z % k)
    let d := ix hk j
    have he : bits W i = xo (x p) (bits (V k) d) := by
      funext w
      change (tableIndex (keyBit3 z (X k q z seed w) (V k w))).testBit i = _
      rw [bit_pack]
      simp only [keyBit3, xo, x, p, ix, bits, d, j, Nat.mod_mod]
    rw [he]
    exact xorG (Or.inr (Or.inl ⟨p, rfl⟩)) (Or.inl (bitV k d))
  have wlt (w : Fin (k + k) → Bool) : W w < 2 ^ k := pack_lt _
  let R := Set.range (fun i : Fin k => bits (fun w => rowWord k (W w) (U k w) 3) i)
  have HR : Build (A ∪ (C ∪ K)) R (4 * k + 19 * k * 3) :=
    rowSchedule hk W (U k) wlt (U_lt k) (fun i => Or.inr (Or.inr ⟨i, rfl⟩))
      (fun i => Or.inl (bitU k i)) 3
  let h := k - (k + 1) / 2
  let rl : Sig (k + k) := fun w => decide (rowWord k (W w) (U k w) 3 < 2 ^ h)
  let cl : Sig (k + k) := fun w => decide (colWord k (W w) (V k w) 3 < 2 ^ h)
  let E := ((C ∪ K) ∪ R)
  have hf : (fun _ => false) ∈ A := Or.inr (by simp)
  have allCol (i : Fin k) : bits (fun w => colWord k (W w) (V k w) 3) i ∈ A ∪ E := by
    let p := ix hk (i.val + k - (z + 7) % k)
    have he : (z + (p.val + (2 * 3 + 1))) % k = i.val := by
      rw [show z + (p.val + (2 * 3 + 1)) = (z + 7) + p.val by omega]
      exact mod_inverse' hk i.isLt
    apply Or.inr ∘ Or.inl ∘ Or.inl ∘ Or.inr
    refine ⟨p, ?_⟩
    funext w
    have J := colWord_norm hk20 (wlt w) (V_lt k w) hz 3 le_rfl p.val
    simp only [coordBit, he] at J
    change col (fun j => v (ix hk j) w) (fun t j => c t (ix hk j)) (fun j => x (ix hk j) w) 3 p.val =
      (colWord k (W w) (V k w) 3).testBit i
    rw [J]
    have ev : (fun j => v (ix hk j) w) = coordBit k z (V k w) :=
      funext fun _ => coord_shift
    have ec : (fun t j => c t (ix hk j)) = coordConst3 k z :=
      funext fun _ => funext fun _ => const3_shift
    have ex : (fun j => x (ix hk j) w) = coordBit k z (colWord k (W w) (V k w) 0) :=
      funext fun j => (key3_coord (by omega) (V_lt k w) _ j).symm
    rw [ev, ec, ex]
  have Hrl : Build (A ∪ E) {rl} (k + 1) := thresholds h _
    (fun w => rowWord_lt (U_lt k w) 3) (fun i _ => Or.inr (Or.inr ⟨i, rfl⟩)) (Or.inl hf)
  have Hcl : Build (A ∪ (E ∪ {rl})) {cl} (k + 1) := thresholds h _
    (fun w => colWord_lt (V_lt k w) 3) (fun i _ => (allCol i).elim Or.inl (fun h => Or.inr (Or.inl h))) (Or.inl hf)
  have HA : Build (A ∪ ((E ∪ {rl}) ∪ {cl})) {accept k q z seed} 1 :=
    andG (f := rl) (g := cl) (by simp) (by simp)
  refine relax (seq (seq (seq (seq (seq HC HK) HR) Hrl) Hcl) HA) le_rfl ?_ ?_
  · exact Set.subset_union_right
  · ring_nf; omega

end Slot25483

namespace Result25483

open BitBridge Sweep25483 Word25483 Build25483 Slot25483
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

private theorem any_graph {k q z : Nat} (hk20 : 20 ≤ k)
    (hq : q + 19 ≤ k) (hz : 3 ≤ z) (hz' : z + 7 = k + (k - q)) (qh : q ≤ (k + 1) / 2)
    (v : Fin (k + k) → Bool) :
    (List.range (2 ^ (k - q))).any (fun s => accept k q z s v) =
    (List.range (2 ^ k)).any (fun w =>
      decide (rowWord k w (U k v) 3 < 2 ^ (k - (k + 1) / 2)) &&
      decide (colWord k w (V k v) 3 < 2 ^ (k - (k + 1) / 2))) := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, List.mem_range]
  constructor
  · rintro ⟨s, _, hs⟩
    exact ⟨SKey k q z s v, pack_lt _, hs⟩
  · rintro ⟨w, hw, hw'⟩
    let y := coordBit k z (colWord k w (V k v) 0)
    let s := tableIndex (fun i : Fin (k - q) => y (i.val + q))
    refine ⟨s, pack_lt _, ?_⟩
    have H : SKey k q z s v = w := slotLogic hk20 hq hz hz' qh v hw
      (of_decide_eq_true (Bool.and_eq_true_iff.mp hw').2) fun i hi hik => by
        let j : Fin (k - q) := ⟨i - q, by omega⟩
        exact (bit_pack _ j).trans (congrArg y (Nat.sub_add_cancel hi))
    simpa only [accept, H] using hw'

private theorem solve (k : Nat) (hk20 : 20 ≤ k) :
    ∃ C : Circuit, FanInTwo C ∧ ReadsBack (k + k) C ∧
    C.size ≤ 2 ^ max 19 (k - (k + 1) / 2) * (500 * k) ∧
    ∀ v : Fin (k + k) → Bool, C.eval (List.ofFn v) =
      (List.range (2 ^ k)).any (fun w =>
        decide (rowWord k w (U k v) 3 < 2 ^ (k - (k + 1) / 2)) &&
        decide (colWord k w (V k v) 3 < 2 ^ (k - (k + 1) / 2))) := by
  let q := min ((k + 1) / 2) (k - 19)
  let z := k + (k - q) - 7
  have hq : q + 19 ≤ k := by
    have := min_le_right ((k + 1) / 2) (k - 19)
    omega
  have qh : q ≤ (k + 1) / 2 := min_le_left ..
  have hz : 3 ≤ z := by dsimp [z]; omega
  have hz' : z + 7 = k + (k - q) := by dsimp [z]; omega
  have he : k - q = max 19 (k - (k + 1) / 2) := by
    dsimp [q]
    omega
  let N := 2 ^ (k - q)
  let s := 147 * k + 3
  let F := fun i : Fin N => accept k q z i.val
  let xs := (List.finRange N).map F
  have Hs : Build (base (k + k)) (Set.range F) (N * s) :=
    finG F s (fun i => slotCircuit hk20 hq hz)
  let O : Sig (k + k) := fun v => xs.any (fun f => f v)
  have Ho : Build (base (k + k) ∪ Set.range F) {O} N := by
    simpa only [xs, List.length_map, List.length_finRange] using
      (anyG (A := base (k + k) ∪ Set.range F) xs
        (by intro f hf; obtain ⟨i, _, rfl⟩ := List.mem_map.mp hf; exact Or.inr ⟨i, rfl⟩)
        (Or.inl (Or.inr (by simp))))
  have H : Build (inputs (k + k)) {O} (2 + (N * s + N)) :=
    relax (seq (inputG (k + k)) (seq Hs Ho)) le_rfl
      (Set.singleton_subset_iff.mpr (Or.inr (Or.inr rfl))) le_rfl
  obtain ⟨c, hc, HS⟩ := H.run (GateBridge.start (F := id) (fun i : Fin (k + k) => fun v => v i) (by intros; rfl)) le_rfl
  clear H
  obtain ⟨C, hsize, hread, hfan, hout⟩ := GateBridge.finish HS (Or.inr (Set.mem_singleton O))
  refine ⟨C, hfan, hread, ?_, fun v => ?_⟩
  · rw [hsize, Nat.zero_add, ← he]
    have hn : 1 ≤ N := Nat.two_pow_pos _
    have hslot : s + 3 ≤ 500 * k := by dsimp [s]; omega
    have h := Nat.mul_le_mul_left N hslot
    change c ≤ N * (500 * k)
    calc
      c ≤ 2 + (N * s + N) := hc
      _ ≤ N * (s + 3) := by
        rw [Nat.mul_add N s 3, show N * 3 = N + N + N by omega]
        omega
      _ ≤ N * (500 * k) := h
  · rw [hout]
    have eq : O v = (List.range N).any (fun seed => accept k q z seed v) := by
      apply Bool.eq_iff_iff.mpr
      simp only [O, xs, List.any_eq_true, List.mem_map, List.mem_range, forall_exists_index]
      constructor
      · rintro ⟨_, ⟨i, _, rfl⟩, hh⟩
        exact ⟨i.val, i.isLt, hh⟩
      · rintro ⟨i, hi, hh⟩
        exact ⟨F ⟨i, hi⟩, ⟨⟨i, hi⟩, List.mem_finRange _, rfl⟩, hh⟩
    exact eq.trans (any_graph hk20 hq hz hz' qh v)

end Result25483

end PEqualNP.Outside.L_meta_25483_aux

open PEqualNP.Outside.L_meta_25483_aux.BitBridge PEqualNP.Outside.L_meta_25483_aux.Word25483
open PEqualNP.Outside.L_meta_25483_aux.Slot25483 PEqualNP.Outside.L_meta_25483_aux.Result25483

theorem PEqualNP.Outside.L_meta_25483 : ∀ k : Nat, 20 ≤ k →
  let rot := fun (s word : Nat) =>
    ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k
  let step := fun (word : Nat) =>
    (List.range k).foldl (fun acc i =>
      acc ||| ((xor (word.testBit i)
        (!(word.testBit ((i + 1) % k)) && word.testBit ((i + 2) % k))).toNat <<< i)) 0
  let constant := fun (j : Nat) => 3 ^ (k + j) % 2 ^ k
  let first := fun (rowKey rowName : Nat) =>
    (List.range 3).foldl (fun state i =>
      step (state ^^^ rot 1 state ^^^ rot (k - 1) state) ^^^
        rot (2 * i) rowKey ^^^ constant (i + 1)) (rot 1 rowKey ^^^ rowName)
  let second := fun (colKey colName : Nat) =>
    (List.range 3).foldl (fun state i =>
      step (state ^^^ rot 2 state ^^^ rot (k - 2) state) ^^^
        rot (3 * (i + 1) + 1) colKey ^^^ constant (3 + (i + 1))) (rot 3 colKey ^^^ colName)
  let low := k - (k + 1) / 2
  let graph : Fin (2 ^ k) → Fin (2 ^ k) → Bool := fun row col =>
    (List.range (2 ^ k)).any (fun w =>
      decide (first w row.val < 2 ^ low) && decide (second w col.val < 2 ^ low))
  ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (k + k) C ∧
    C.size ≤ 2 ^ max 19 low * (500 * k) ∧
    ∀ bits : Fin (k + k) → Bool,
      C.eval (List.ofFn bits) = PEqualNP.Represents.adjFun (k := k) (l := k) graph bits := by
  intro k hk20
  have rowEq (w u : Nat) :
      (List.range 3).foldl (fun s t =>
        (List.range k).foldl (fun acc i =>
          acc ||| ((xor ((s ^^^ rot k 1 s ^^^ rot k (k - 1) s).testBit i)
            (!((s ^^^ rot k 1 s ^^^ rot k (k - 1) s).testBit ((i + 1) % k)) &&
             (s ^^^ rot k 1 s ^^^ rot k (k - 1) s).testBit ((i + 2) % k))).toNat <<< i)) 0
          ^^^ rot k (2 * t) w ^^^ constant k (t + 1)) (rot k 1 w ^^^ u) = rowWord k w u 3 := by
    simp only [← wordStep_eq]
    exact round_fold (rowWord k w u) (fun s t => updateRound k 1 (2 * t) (t + 1) w s) (by intros; rfl) 3
  have colEq (w v : Nat) :
      (List.range 3).foldl (fun s t =>
        (List.range k).foldl (fun acc i =>
          acc ||| ((xor ((s ^^^ rot k 2 s ^^^ rot k (k - 2) s).testBit i)
            (!((s ^^^ rot k 2 s ^^^ rot k (k - 2) s).testBit ((i + 1) % k)) &&
             (s ^^^ rot k 2 s ^^^ rot k (k - 2) s).testBit ((i + 2) % k))).toNat <<< i)) 0
          ^^^ rot k (3 * (t + 1) + 1) w ^^^ constant k (3 + (t + 1))) (rot k 3 w ^^^ v) = colWord k w v 3 := by
    simp only [← wordStep_eq]
    exact round_fold (colWord k w v) (fun s t => updateRound k 2 (3 * (t + 1) + 1) (3 + (t + 1)) w s)
      (by intros; rfl) 3
  dsimp only
  obtain ⟨C, hFan, hRead, hSize, hEval⟩ := solve k hk20
  refine ⟨C, hFan, hRead, hSize, fun b => ?_⟩
  rw [hEval]
  unfold PEqualNP.Represents.adjFun
  dsimp only
  simp only [← wordStep_eq] at rowEq colEq ⊢
  change _ = (List.range (2 ^ k)).any (fun w =>
    decide ((List.range 3).foldl (fun s t => wordStep k (s ^^^ rot k 1 s ^^^ rot k (k - 1) s)
      ^^^ rot k (2 * t) w ^^^ constant k (t + 1)) (rot k 1 w ^^^ ((U k b) % 2 ^ k)) < 2 ^ (k - (k + 1) / 2)) &&
    decide ((List.range 3).foldl (fun s t => wordStep k (s ^^^ rot k 2 s ^^^ rot k (k - 2) s)
      ^^^ rot k (3 * (t + 1) + 1) w ^^^ constant k (3 + (t + 1))) (rot k 3 w ^^^ ((V k b) % 2 ^ k)) < 2 ^ (k - (k + 1) / 2)))
  simp only [Nat.mod_eq_of_lt (U_lt k b), Nat.mod_eq_of_lt (V_lt k b), rowEq, colEq]
