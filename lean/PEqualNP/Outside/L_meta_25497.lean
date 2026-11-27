import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25497_aux

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
    refine ⟨i.val, by simp, fun x => ?_⟩
    change (List.ofFn x).getD i.val false = F (input i) x
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn, h i x]

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

namespace Sweep25497

private def mix (x : Nat → Bool) (n : Nat) : Bool :=
  xor (xor (x n) (x (n + 1))) (x (n + 2))

private def core (x : Nat → Bool) (n : Nat) : Bool :=
  xor (mix x n) (!(mix x (n + 1)) && mix x (n + 2))

private def pivot1 (u c1 : Nat → Bool) (x : Nat → Bool) (n : Nat) : Bool :=
  xor (xor (xor (x (n + 1)) (!(mix x (n + 1)) && mix x (n + 2))) (u (n + 2))) (c1 n)

private def step1 (u c1 : Nat → Bool) (x : Nat → Bool) (n : Nat) : Bool :=
  xor (xor (core x n) (xor (x (n + 2)) (u (n + 2)))) (c1 n)

private theorem step1_eq_xor_pivot1 {u c1 x : Nat → Bool} {n : Nat} :
    step1 u c1 x n = xor (x n) (pivot1 u c1 x n) := by
  unfold step1 pivot1 core mix
  cases x n <;> cases x (n + 1) <;> cases x (n + 2) <;> cases x (n + 3) <;> cases x (n + 4) <;>
    cases u (n + 2) <;> cases c1 n <;> decide

private theorem pivot1_congr {u c1 x y : Nat → Bool} {n : Nat}
    (H : ∀ i, n + 1 ≤ i → i ≤ n + 4 → x i = y i) :
    pivot1 u c1 x n = pivot1 u c1 y n := by
  unfold pivot1 mix
  rw [H (n + 1) (by omega) (by omega), H (n + 2) (by omega) (by omega),
    H (n + 3) (by omega) (by omega), H (n + 4) (by omega) (by omega)]

private theorem step1_congr {u c1 x y : Nat → Bool} {n : Nat}
    (H : ∀ i, n ≤ i → i ≤ n + 4 → x i = y i) :
    step1 u c1 x n = step1 u c1 y n := by
  unfold step1 core mix
  rw [H n (by omega) (by omega), H (n + 1) (by omega) (by omega),
    H (n + 2) (by omega) (by omega), H (n + 3) (by omega) (by omega),
    H (n + 4) (by omega) (by omega)]

private def step2 (u c1 c2 : Nat → Bool) (x : Nat → Bool) (n : Nat) : Bool :=
  xor (xor (core (step1 u c1 x) n) (xor (x (n + 1)) (u (n + 1)))) (c2 n)

private def mix1Piv (u c1 : Nat → Bool) (x : Nat → Bool) (n : Nat) : Bool :=
  xor (xor (pivot1 u c1 x n) (step1 u c1 x (n + 1))) (step1 u c1 x (n + 2))

private def pivot2 (u c1 c2 : Nat → Bool) (x : Nat → Bool) (n : Nat) : Bool :=
  xor (xor (xor (mix1Piv u c1 x n) (!(mix (step1 u c1 x) (n + 1)) && mix (step1 u c1 x) (n + 2)))
    (xor (x (n + 1)) (u (n + 1)))) (c2 n)

private theorem pivot2_congr {u c1 c2 x y : Nat → Bool} {n : Nat}
    (H : ∀ i, n + 1 ≤ i → i ≤ n + 8 → x i = y i) :
    pivot2 u c1 c2 x n = pivot2 u c1 c2 y n := by
  unfold pivot2 mix1Piv mix
  rw [pivot1_congr (fun i h1 h2 => H i (by omega) (by omega)),
    step1_congr (n := n + 1) (fun i h1 h2 => H i (by omega) (by omega)),
    step1_congr (n := n + 2) (fun i h1 h2 => H i (by omega) (by omega)),
    step1_congr (n := n + 3) (fun i h1 h2 => H i (by omega) (by omega)),
    step1_congr (n := n + 4) (fun i h1 h2 => H i (by omega) (by omega)),
    H (n + 1) (by omega) (by omega)]

private theorem step2_zero_iff {u c1 c2 x : Nat → Bool} {n : Nat} :
    step2 u c1 c2 x n = false ↔ x n = pivot2 u c1 c2 x n := by
  unfold step2 pivot2 mix1Piv core mix
  rw [step1_eq_xor_pivot1 (n := n)]
  cases x n <;> cases pivot1 u c1 x n <;> cases step1 u c1 x (n + 1) <;>
    cases step1 u c1 x (n + 2) <;> cases step1 u c1 x (n + 3) <;>
    cases step1 u c1 x (n + 4) <;> cases x (n + 1) <;> cases u (n + 1) <;>
    cases c2 n <;> decide

private def fill (u c1 c2 : Nat → Bool) : Nat → (Nat → Bool) → (Nat → Bool)
  | 0, x => x
  | n + 1, x => fill u c1 c2 n (Function.update x n (pivot2 u c1 c2 x n))

private theorem fill_ge {u c1 c2 q x i} (H : q ≤ i) : fill u c1 c2 q x i = x i := by
  induction q generalizing x with
  | zero => rfl
  | succ q IH =>
    rw [fill, IH (by omega)]
    exact Function.update_of_ne (by omega) _ _

private theorem fill_lt {u c1 c2 q x i} (H : i < q) :
    fill u c1 c2 q x i = pivot2 u c1 c2 (fill u c1 c2 q x) i := by
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

private theorem fill_unique {u c1 c2 q k x y} (hq : q + 8 ≤ k)
    (hseed : ∀ i, q ≤ i → i < k → x i = y i)
    (hx : ∀ i < q, x i = pivot2 u c1 c2 x i)
    (hy : ∀ i < q, y i = pivot2 u c1 c2 y i) :
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

end Sweep25497

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
      cases hp : p i <;> simp
    · cases hp : p j <;> simp [hji, Ne.symm hji]

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

namespace Word25497

open BitBridge Sweep25497
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
      cases h : x (Fin.last n) <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · rw [Nat.add_zero, Nat.testBit_lt_two_pow hlt]
      · rw [Nat.add_comm, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hlt]
        rfl
    · change (tableIndex (fun i : Fin n => x i.castSucc) +
        (if x (Fin.last n) = true then 2 ^ n else 0)).testBit j.val = x j.castSucc
      cases h : x (Fin.last n) <;> simp only [Bool.false_eq_true, ↓reduceIte]
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
  | t + 1 => updateRound k 2 (3 * (t + 1) + 1) (2 + (t + 1)) w (colWord k w v t)

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

private def coordBit (k z w : Nat) (i : Nat) : Bool := w.testBit ((z + i) % k)

private theorem rowWord1_norm {k z w u : Nat} (hk : 16 ≤ k)
    (hw : w < 2 ^ k) (hu : u < 2 ^ k) (hz : 3 ≤ z) (i : Nat) :
    coordBit k z (rowWord k w u 1) (i + 1) =
      step1 (coordBit k z u) (fun j => coordBit k z (constant k 1) (j + 1))
        (coordBit k z (rowWord k w u 0)) i := by
  have hk0 : 0 < k := by omega
  let p := z + i
  have hi : (p + 1) % k < k := Nat.mod_lt _ hk0
  have hlin (j : Nat) :
      ((rowWord k w u 0) ^^^ rot k 1 (rowWord k w u 0) ^^^
        rot k (k - 1) (rowWord k w u 0)).testBit ((p + j + 1) % k) =
      mix (coordBit k z (rowWord k w u 0)) (i + j) := by
    have hm := Nat.mod_lt (p + j + 1) hk0
    have hs : ((p + j + 1) % k + k - 1) % k = (p + j) % k := by
      rw [sub_cyclic (by omega) (by dsimp [p]; omega)]; simp
    have hs' : ((p + j + 1) % k + k - (k - 1)) % k = (p + j + 2) % k := by
      rw [show (p + j + 1) % k + k - (k - 1) = (p + j + 1) % k + 1 by omega, Nat.mod_add_mod]
    rw [Nat.testBit_xor, Nat.testBit_xor, rbit hm (by omega) (rowWord_lt hu 0),
      rbit hm (by omega) (rowWord_lt hu 0), hs, hs']
    simp only [mix, coordBit, p, Nat.add_assoc]
    have e0 : z + (i + j) = z + i + j := by omega
    have e1 : z + (i + (j + 1)) = z + i + j + 1 := by omega
    have e2 : z + (i + (j + 2)) = z + i + j + 2 := by omega
    rw [e0, e1, e2]
    cases (rowWord k w u 0).testBit ((z + i + j) % k) <;>
      cases (rowWord k w u 0).testBit ((z + i + j + 1) % k) <;>
      cases (rowWord k w u 0).testBit ((z + i + j + 2) % k) <;> rfl
  have hkey :
      (rot k 0 w).testBit ((p + 1) % k) =
        xor (coordBit k z (rowWord k w u 0) (i + 2)) (coordBit k z u (i + 2)) := by
    rw [rbit hi (by omega) hw, sub_cyclic (by omega) (by dsimp [p]; omega)]
    simp only [coordBit, rowWord, Nat.testBit_xor]
    rw [rbit (Nat.mod_lt _ hk0) (by omega) hw, sub_cyclic (by omega) (by omega)]
    have he : p + 1 - 0 = z + (i + 2) - 1 := by dsimp [p]; omega
    rw [he]
    cases w.testBit ((z + (i + 2) - 1) % k) <;> cases u.testBit ((z + (i + 2)) % k) <;> rfl
  have e1 : z + (i + 1) = p + 1 := by dsimp [p]; omega
  change (rowWord k w u (0 + 1)).testBit ((z + (i + 1)) % k) = _
  rw [e1]
  conv_lhs => unfold rowWord updateRound
  rw [Nat.testBit_xor, Nat.testBit_xor, testBit_wordStep hi]
  rw [show ((p + 1) % k + 1) % k = (p + 1 + 1) % k by rw [Nat.mod_add_mod],
    show ((p + 1) % k + 2) % k = (p + 2 + 1) % k by rw [Nat.mod_add_mod]]
  rw [show (p + 1) % k = (p + 0 + 1) % k by rfl, hlin 0, hlin 1, hlin 2]
  simp only [Nat.add_zero]
  rw [show 2 * 0 = 0 by rfl, hkey]
  simp only [step1, core, coordBit, e1]

private theorem rowWord2_norm {k z w u : Nat} (hk : 16 ≤ k)
    (hw : w < 2 ^ k) (hu : u < 2 ^ k) (hz : 3 ≤ z) (i : Nat) :
    coordBit k z (rowWord k w u 2) (i + 2) =
      step2 (coordBit k z u) (fun j => coordBit k z (constant k 1) (j + 1))
        (fun j => coordBit k z (constant k 2) (j + 2))
        (coordBit k z (rowWord k w u 0)) i := by
  have hk0 : 0 < k := by omega
  let p := z + i + 1
  have hi : (p + 1) % k < k := Nat.mod_lt _ hk0
  have hlin (j : Nat) :
      (rowWord k w u 1 ^^^ rot k 1 (rowWord k w u 1) ^^^
        rot k (k - 1) (rowWord k w u 1)).testBit ((p + j + 1) % k) =
      mix (step1 (coordBit k z u) (fun l => coordBit k z (constant k 1) (l + 1))
        (coordBit k z (rowWord k w u 0))) (i + j) := by
    have hm := Nat.mod_lt (p + j + 1) hk0
    have hs : ((p + j + 1) % k + k - 1) % k = (p + j) % k := by
      rw [sub_cyclic (by omega) (by dsimp [p]; omega)]; simp
    have hs' : ((p + j + 1) % k + k - (k - 1)) % k = (p + j + 2) % k := by
      rw [show (p + j + 1) % k + k - (k - 1) = (p + j + 1) % k + 1 by omega, Nat.mod_add_mod]
    rw [Nat.testBit_xor, Nat.testBit_xor, rbit hm (by omega) (rowWord_lt hu 1),
      rbit hm (by omega) (rowWord_lt hu 1), hs, hs']
    have H (d : Nat) := rowWord1_norm (k := k) (z := z) (w := w) (u := u) hk hw hu hz (i + j + d)
    simp only [coordBit] at H
    have he (d : Nat) : z + (i + j + d + 1) = p + j + d := by dsimp [p]; omega
    have H' (d : Nat) : (rowWord k w u 1).testBit ((p + j + d) % k) =
        step1 (coordBit k z u) (fun l => coordBit k z (constant k 1) (l + 1))
          (coordBit k z (rowWord k w u 0)) (i + j + d) := by
      rw [← he d]; exact H d
    rw [show (p + j) % k = (p + j + 0) % k by rfl, H' 0, H' 1, H' 2]
    simp only [mix, Nat.add_assoc, Nat.add_zero]
    cases step1 (coordBit k z u) (fun l => coordBit k z (constant k 1) (l + 1)) (coordBit k z (rowWord k w u 0)) (i + j) <;>
      cases step1 (coordBit k z u) (fun l => coordBit k z (constant k 1) (l + 1)) (coordBit k z (rowWord k w u 0)) (i + (j + 1)) <;>
      cases step1 (coordBit k z u) (fun l => coordBit k z (constant k 1) (l + 1)) (coordBit k z (rowWord k w u 0)) (i + (j + 2)) <;> rfl
  have hkey :
      (rot k 2 w).testBit ((p + 1) % k) =
        xor (coordBit k z (rowWord k w u 0) (i + 1)) (coordBit k z u (i + 1)) := by
    rw [rbit hi (by omega) hw, sub_cyclic (by omega) (by dsimp [p]; omega)]
    simp only [coordBit, rowWord, Nat.testBit_xor]
    rw [rbit (Nat.mod_lt _ hk0) (by omega) hw, sub_cyclic (by omega) (by omega)]
    have he : p + 1 - 2 = z + (i + 1) - 1 := by dsimp [p]; omega
    rw [he]
    cases w.testBit ((z + (i + 1) - 1) % k) <;> cases u.testBit ((z + (i + 1)) % k) <;> rfl
  have e2 : z + (i + 2) = p + 1 := by dsimp [p]; omega
  change (rowWord k w u (1 + 1)).testBit ((z + (i + 2)) % k) = _
  rw [e2]
  conv_lhs => unfold rowWord updateRound
  rw [Nat.testBit_xor, Nat.testBit_xor, testBit_wordStep hi]
  rw [show ((p + 1) % k + 1) % k = (p + 1 + 1) % k by rw [Nat.mod_add_mod],
    show ((p + 1) % k + 2) % k = (p + 2 + 1) % k by rw [Nat.mod_add_mod]]
  rw [show (p + 1) % k = (p + 0 + 1) % k by rfl, hlin 0, hlin 1, hlin 2]
  simp only [Nat.add_zero]
  rw [show 2 * 1 = 2 by rfl, hkey]
  simp only [step2, core, coordBit, e2]

end Word25497

namespace Build25497

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

private theorem pivotG {A : Set (Sig n)} {a b c u : Sig n}
    (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) (hu : u ∈ A) (d : Bool) :
    Build A {fun v => xor (xor (xor (a v) (!(b v) && c v)) (u v)) d} 11 := by
  let f := xo a (an (nt b) c)
  have H₁ : Build A {f} 6 := nonlinG ha hb hc
  let g := xo f u
  have H₂ : Build (A ∪ {f}) {g} 4 := xorG (Or.inr rfl) (Or.inl hu)
  have H₃ := flipG (A := A ∪ ({f} ∪ {g})) (f := g) (by simp) d
  exact relax (seq (seq H₁ H₂) H₃) le_rfl (Set.singleton_subset_iff.mpr (Or.inr rfl)) le_rfl

private theorem rowG {A : Set (Sig n)} {a b c x u : Sig n}
    (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) (hx : x ∈ A) (hu : u ∈ A) (d : Bool) :
    Build A {fun v => xor (xor (xor (a v) (!(b v) && c v)) (xor (x v) (u v))) d} 15 := by
  let w := xo x u
  have H₁ : Build A {w} 4 := xorG hx hu
  have H₂ := pivotG (A := A ∪ {w}) (Or.inl ha) (Or.inl hb) (Or.inl hc) (Or.inr rfl) d
  exact relax (seq H₁ H₂) le_rfl (Set.singleton_subset_iff.mpr (Or.inr rfl)) le_rfl

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

end Build25497

namespace RowCircuit25497

open Sweep25497 Build25497

private def ix {k : Nat} (hk : 0 < k) (i : Nat) : Fin k := ⟨i % k, Nat.mod_lt _ hk⟩

private theorem ix_add {k : Nat} (hk : 0 < k) (i j : Nat) :
    ix hk (i % k + j) = ix hk (i + j) := Fin.ext (Nat.mod_add_mod ..)

private def lift3 (R : Nat → Nat) (n : Nat) : Nat :=
  max (max (R n) (R (n + 1))) (R (n + 2))

private def rP1 (R : Nat → Nat) (n : Nat) : Nat :=
  max (lift3 R (n + 1)) (lift3 R (n + 2))

private def rS1 (R : Nat → Nat) (n : Nat) : Nat :=
  max (R n) (rP1 R n)

private def rM1p (R : Nat → Nat) (n : Nat) : Nat :=
  max (max (rP1 R n) (rS1 R (n + 1))) (rS1 R (n + 2))

private def rM1 (R : Nat → Nat) (n : Nat) : Nat :=
  lift3 (rS1 R) n

private def rS2 (R : Nat → Nat) (n : Nat) : Nat :=
  max (lift3 (rM1 R) n) (R (n + 1))

private def point (k q n : Nat) : Nat :=
  if n % k < q then q - n % k else 0

private theorem point_lt {k q n j : Nat} (hq : q + 8 ≤ k) (hn : n < q)
    (hj1 : n + 1 ≤ j) (hj2 : j ≤ n + 8) : point k q j < point k q n := by
  have hn' : point k q n = q - n := by
    simp [point, Nat.mod_eq_of_lt (by omega : n < k), hn]
  rw [hn']
  unfold point
  by_cases hjk : j < k
  · rw [Nat.mod_eq_of_lt hjk]
    split <;> omega
  · have hjmod : j % k < q := by
      rw [Nat.mod_eq_sub_mod (by omega : k ≤ j), Nat.mod_eq_of_lt (by omega : j - k < k)]
      omega
    have hge : q ≤ j % k := by
      rw [Nat.mod_eq_sub_mod (by omega : k ≤ j), Nat.mod_eq_of_lt (by omega : j - k < k)]
      omega
    omega

private theorem point_lt' {k q n j : Nat} (hq : q + 8 ≤ k) (hn : n < q)
    (hj1 : n + 1 ≤ j) (hj2 : j ≤ n + 8) : point k q j < q - n := by
  have hn' : point k q n = q - n := by
    simp [point, Nat.mod_eq_of_lt (by omega : n < k), hn]
  unfold point
  by_cases hjk : j < k
  · rw [Nat.mod_eq_of_lt hjk]
    split <;> omega
  · have hjmod : j % k = j - k := by
      rw [Nat.mod_eq_sub_mod (by omega : k ≤ j), Nat.mod_eq_of_lt (by omega : j - k < k)]
    rw [hjmod]
    split <;> omega

private theorem rank_add {M a b c d : Nat} (hab : a ≤ b) (hcd : c < d) :
    a * M + c < b * M + d := by
  have := Nat.mul_le_mul_right M hab
  omega

private theorem rank_next {M a b c d : Nat} (hab : a < b) (hc : c < M) :
    a * M + c < b * M + d := by
  have H := Nat.mul_le_mul_right M (Nat.succ_le_of_lt hab)
  rw [Nat.succ_mul] at H
  omega

private theorem lift3_le {R : Nat → Nat} {n b : Nat}
    (H : ∀ j, n ≤ j → j ≤ n + 2 → R j ≤ b) : lift3 R n ≤ b := by
  unfold lift3
  exact max_le (max_le (H _ (by omega) (by omega)) (H _ (by omega) (by omega))) (H _ (by omega) (by omega))

private theorem rP1_le {R : Nat → Nat} {n b : Nat}
    (H : ∀ j, n + 1 ≤ j → j ≤ n + 4 → R j ≤ b) : rP1 R n ≤ b := by
  unfold rP1
  exact max_le (lift3_le fun j h1 h2 => H j (by omega) (by omega))
    (lift3_le fun j h1 h2 => H j (by omega) (by omega))

private theorem rS1_le {R : Nat → Nat} {n b : Nat}
    (H : ∀ j, n ≤ j → j ≤ n + 4 → R j ≤ b) : rS1 R n ≤ b := by
  unfold rS1
  exact max_le (H n (by omega) (by omega)) (rP1_le fun j h1 h2 => H j (by omega) (by omega))

private theorem rM1p_le {R : Nat → Nat} {n b : Nat}
    (H : ∀ j, n + 1 ≤ j → j ≤ n + 6 → R j ≤ b) : rM1p R n ≤ b := by
  unfold rM1p
  exact max_le (max_le (rP1_le fun j h1 h2 => H j (by omega) (by omega))
    (rS1_le fun j h1 h2 => H j (by omega) (by omega)))
    (rS1_le fun j h1 h2 => H j (by omega) (by omega))

private theorem rM1_le {R : Nat → Nat} {n b : Nat}
    (H : ∀ j, n ≤ j → j ≤ n + 6 → R j ≤ b) : rM1 R n ≤ b := by
  unfold rM1
  exact lift3_le fun j h1 h2 => rS1_le fun l hl1 hl2 => H l (by omega) (by omega)

private theorem lift3_ge (R : Nat → Nat) (i d : Nat) (hd : d ≤ 2) : R (i + d) ≤ lift3 R i := by
  interval_cases d <;> simp [lift3]

private inductive Kind where
  | x | m0 | p1 | s1 | m1p | m1 | s2
  deriving DecidableEq

private def allKinds : List Kind := [.x, .m0, .p1, .s1, .m1p, .m1, .s2]

private instance : Fintype Kind where
  elems := ⟨allKinds, by decide⟩
  complete := fun k => by cases k <;> decide

private def kindCost : Kind → Nat
  | .x => 15
  | .m0 => 8
  | .p1 => 11
  | .s1 => 4
  | .m1p => 8
  | .m1 => 8
  | .s2 => 15

private theorem sum_kindCost : ∑ kd : Kind, kindCost kd = 69 := by decide

private theorem node_cost (k : Nat) : ∑ a : Kind × Fin k, kindCost a.1 = 69 * k := by
  rw [Fintype.sum_prod_type]
  have h1 : ∀ kd : Kind, ∑ _i : Fin k, kindCost kd = k * kindCost kd := fun kd => by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  simp_rw [h1, ← Finset.mul_sum, sum_kindCost, Nat.mul_comm]

private theorem rowSweep2Schedule {k q n : Nat} (hk : 0 < k) (hq : q + 8 ≤ k)
    {A : Set (Sig n)} (x u : Fin k → Sig n) (c1 c2 : Fin k → Bool)
    (hu : ∀ i, u i ∈ A) (hs : ∀ i : Fin k, q ≤ i.val → x i ∈ A)
    (hp : ∀ (i : Fin k), i.val < q → ∀ b,
      x i b = pivot2 (fun j => u (ix hk j) b) (fun j => c1 (ix hk j)) (fun j => c2 (ix hk j))
        (fun j => x (ix hk j) b) i.val) :
    Build A (Set.range x ∪ Set.range (fun i : Fin k => fun b =>
      step2 (fun j => u (ix hk j) b) (fun j => c1 (ix hk j)) (fun j => c2 (ix hk j))
        (fun j => x (ix hk j) b) i.val)) (69 * k) := by
  let R := point k q
  let Uf (b : Fin n → Bool) (j : Nat) : Bool := u (ix hk j) b
  let C1f (j : Nat) : Bool := c1 (ix hk j)
  let C2f (j : Nat) : Bool := c2 (ix hk j)
  let Xf (b : Fin n → Bool) (j : Nat) : Bool := x (ix hk j) b
  let M0 (i : Nat) : Sig n := fun b => mix (Xf b) i
  let P1 (i : Nat) : Sig n := fun b => pivot1 (Uf b) C1f (Xf b) i
  let S1 (i : Nat) : Sig n := fun b => step1 (Uf b) C1f (Xf b) i
  let M1p (i : Nat) : Sig n := fun b => mix1Piv (Uf b) C1f (Xf b) i
  let M1 (i : Nat) : Sig n := fun b => mix (S1 · b) i
  let S2 (i : Nat) : Sig n := fun b => step2 (Uf b) C1f C2f (Xf b) i
  let F : Kind × Fin k → Sig n
    | (.x, i) => x i
    | (.m0, i) => M0 i
    | (.p1, i) => P1 i
    | (.s1, i) => S1 i
    | (.m1p, i) => M1p i
    | (.m1, i) => M1 i
    | (.s2, i) => S2 i
  let rk : Kind × Fin k → Nat
    | (.x, i) => R i * 10 + 0
    | (.m0, i) => lift3 R i * 10 + 1
    | (.p1, i) => rP1 R i * 10 + 2
    | (.s1, i) => rS1 R i * 10 + 3
    | (.m1p, i) => rM1p R i * 10 + 4
    | (.m1, i) => rM1 R i * 10 + 5
    | (.s2, i) => rS2 R i * 10 + 6
  have rm (i : Nat) : R (i % k) = R i := by simp [R, point]
  have radd (i j : Nat) : R (i % k + j) = R (i + j) := by rw [← rm (i % k + j), ← rm (i + j), Nat.mod_add_mod]
  have l3m (G : Nat → Nat) (hG : ∀ i, G (i % k) = G i) (i : Nat) : lift3 G (i % k) = lift3 G i := by
    have ga (j : Nat) : G (i % k + j) = G (i + j) := by rw [← hG (i % k + j), ← hG (i + j), Nat.mod_add_mod]
    unfold lift3; rw [hG, ga 1, ga 2]
  have l3a (G : Nat → Nat) (hG : ∀ i, G (i % k) = G i) (i j : Nat) : lift3 G (i % k + j) = lift3 G (i + j) := by
    rw [← l3m G hG (i % k + j), ← l3m G hG (i + j), Nat.mod_add_mod]
  have rp1m (i : Nat) : rP1 R (i % k) = rP1 R i := by unfold rP1; rw [l3a R rm, l3a R rm]
  have rs1m (i : Nat) : rS1 R (i % k) = rS1 R i := by unfold rS1; rw [rm, rp1m]
  have rs1a (i j : Nat) : rS1 R (i % k + j) = rS1 R (i + j) := by rw [← rs1m (i % k + j), ← rs1m (i + j), Nat.mod_add_mod]
  have rm1pm (i : Nat) : rM1p R (i % k) = rM1p R i := by unfold rM1p; rw [rp1m, rs1a, rs1a]
  have rm1m (i : Nat) : rM1 R (i % k) = rM1 R i := l3m (rS1 R) rs1m i
  have xfm (b : Fin n → Bool) (i : Nat) : Xf b (i % k) = Xf b i := by simp [Xf, ix]
  have xfa (b : Fin n → Bool) (i j : Nat) : Xf b (i % k + j) = Xf b (i + j) := by simp [Xf, ix, Nat.mod_add_mod]
  have ufa (b : Fin n → Bool) (i j : Nat) : Uf b (i % k + j) = Uf b (i + j) := by simp [Uf, ix, Nat.mod_add_mod]
  have c1m (i : Nat) : C1f (i % k) = C1f i := by simp [C1f, ix]
  have m0m (i : Nat) : M0 (i % k) = M0 i := by funext b; unfold M0 mix; rw [xfm, xfa, xfa]
  have m0a (i j : Nat) : M0 (i % k + j) = M0 (i + j) := by rw [← m0m (i % k + j), ← m0m (i + j), Nat.mod_add_mod]
  have p1m (i : Nat) : P1 (i % k) = P1 i := by
    funext b; unfold P1 pivot1; rw [xfa, ufa, c1m]
    have h1 : mix (Xf b) (i % k + 1) = mix (Xf b) (i + 1) := congrFun (m0a i 1) b
    have h2 : mix (Xf b) (i % k + 2) = mix (Xf b) (i + 2) := congrFun (m0a i 2) b
    rw [h1, h2]
  have s1m (i : Nat) : S1 (i % k) = S1 i := by
    funext b
    change step1 (Uf b) C1f (Xf b) (i % k) = step1 (Uf b) C1f (Xf b) i
    rw [step1_eq_xor_pivot1, step1_eq_xor_pivot1, xfm]
    have hp1 := congrFun (p1m i) b
    exact congrArg (xor (Xf b i)) hp1
  have s1a (i j : Nat) : S1 (i % k + j) = S1 (i + j) := by rw [← s1m (i % k + j), ← s1m (i + j), Nat.mod_add_mod]
  have m1pm (i : Nat) : M1p (i % k) = M1p i := by
    funext b; unfold M1p mix1Piv
    have hp1 : pivot1 (Uf b) C1f (Xf b) (i % k) = pivot1 (Uf b) C1f (Xf b) i := congrFun (p1m i) b
    have hs1 : step1 (Uf b) C1f (Xf b) (i % k + 1) = step1 (Uf b) C1f (Xf b) (i + 1) := congrFun (s1a i 1) b
    have hs2 : step1 (Uf b) C1f (Xf b) (i % k + 2) = step1 (Uf b) C1f (Xf b) (i + 2) := congrFun (s1a i 2) b
    rw [hp1, hs1, hs2]
  have m1m (i : Nat) : M1 (i % k) = M1 i := by
    funext b; unfold M1 mix; dsimp only
    have h0 : S1 (i % k) b = S1 i b := congrFun (s1m i) b
    have h1 : S1 (i % k + 1) b = S1 (i + 1) b := congrFun (s1a i 1) b
    have h2 : S1 (i % k + 2) b = S1 (i + 2) b := congrFun (s1a i 2) b
    rw [h0, h1, h2]
  let Earlier (l : Nat) : Set (Sig n) := A ∪ {f | ∃ j ∈ (Finset.univ : Finset (Kind × Fin k)), rk j < l ∧ f = F j}
  have hasX (i l : Nat) (H : R i * 10 + 0 < l) : x (ix hk i) ∈ Earlier l :=
    Or.inr ⟨(.x, ix hk i), Finset.mem_univ _, by simpa [rk, ix, rm] using H, rfl⟩
  have hasM0 (i l : Nat) (H : lift3 R i * 10 + 1 < l) : M0 i ∈ Earlier l :=
    Or.inr ⟨(.m0, ix hk i), Finset.mem_univ _, by simpa [rk, ix, l3m R rm] using H, (m0m i).symm⟩
  have hasP1 (i l : Nat) (H : rP1 R i * 10 + 2 < l) : P1 i ∈ Earlier l :=
    Or.inr ⟨(.p1, ix hk i), Finset.mem_univ _, by simpa [rk, ix, rp1m] using H, (p1m i).symm⟩
  have hasS1 (i l : Nat) (H : rS1 R i * 10 + 3 < l) : S1 i ∈ Earlier l :=
    Or.inr ⟨(.s1, ix hk i), Finset.mem_univ _, by simpa [rk, ix, rs1m] using H, (s1m i).symm⟩
  have hasM1p (i l : Nat) (H : rM1p R i * 10 + 4 < l) : M1p i ∈ Earlier l :=
    Or.inr ⟨(.m1p, ix hk i), Finset.mem_univ _, by simpa [rk, ix, rm1pm] using H, (m1pm i).symm⟩
  have hasM1 (i l : Nat) (H : rM1 R i * 10 + 5 < l) : M1 i ∈ Earlier l :=
    Or.inr ⟨(.m1, ix hk i), Finset.mem_univ _, by simpa [rk, ix, rm1m] using H, (m1m i).symm⟩
  have Hb (nd : Kind × Fin k) : Build (Earlier (rk nd)) {F nd} (kindCost nd.1) := by
    rcases nd with ⟨kd, i⟩
    cases kd with
    | x =>
      by_cases hi : i.val < q
      · have hRi : R i = q - i.val := by simp [R, point, Nat.mod_eq_of_lt i.isLt, hi]
        have hR_lt (j : Nat) (h1 : i.val + 1 ≤ j) (h2 : j ≤ i.val + 8) : R j ≤ R i - 1 := by
          have h : R j < q - i.val := point_lt' hq hi h1 h2
          omega
        have hRi_pos : 0 < R i := by omega
        have hm1p : M1p i ∈ Earlier (rk (.x, i)) := hasM1p i _ (rank_next (by
          have := rM1p_le (R := R) (n := i.val) (b := R i - 1) (fun j h1 h2 => hR_lt j h1 (by omega))
          omega) (by omega))
        have hm1_1 : M1 (i.val + 1) ∈ Earlier (rk (.x, i)) := hasM1 (i.val + 1) _ (rank_next (by
          have := rM1_le (R := R) (n := i.val + 1) (b := R i - 1) (fun j h1 h2 => hR_lt j (by omega) (by omega))
          omega) (by omega))
        have hm1_2 : M1 (i.val + 2) ∈ Earlier (rk (.x, i)) := hasM1 (i.val + 2) _ (rank_next (by
          have := rM1_le (R := R) (n := i.val + 2) (b := R i - 1) (fun j h1 h2 => hR_lt j (by omega) (by omega))
          omega) (by omega))
        have hx1 : x (ix hk (i.val + 1)) ∈ Earlier (rk (.x, i)) := hasX (i.val + 1) _ (rank_next (by
          have := hR_lt (i.val + 1) (by omega) (by omega); omega) (by omega))
        have H := rowG hm1p hm1_1 hm1_2 hx1 (Or.inl (hu (ix hk (i.val + 1)))) (c2 (ix hk i))
        have he : x i = (fun b => xor (xor (xor (M1p i b) (!(M1 (i.val + 1) b) && M1 (i.val + 2) b))
            (xor (x (ix hk (i.val + 1)) b) (u (ix hk (i.val + 1)) b))) (c2 (ix hk i))) := by
          funext b
          have hpi := hp i hi b
          simpa [M1p, M1, S1, Uf, C1f, C2f, Xf, pivot2] using hpi
        simpa only [F, kindCost, he] using H
      · exact relax (idle (Set.singleton_subset_iff.mpr (Or.inl (hs i (by omega)) : x i ∈ Earlier (rk (.x, i))))) le_rfl le_rfl (by simp [kindCost])
    | m0 =>
      have hx (d : Nat) (hd : d ≤ 2) : x (ix hk (i.val + d)) ∈ Earlier (rk (.m0, i)) :=
        hasX (i.val + d) _ (rank_add (lift3_ge R i d hd) (by omega))
      exact mixG (hx 0 (by omega)) (hx 1 (by omega)) (hx 2 (by omega))
    | p1 =>
      have hx1 : x (ix hk (i.val + 1)) ∈ Earlier (rk (.p1, i)) :=
        hasX (i.val + 1) _ (rank_add ((lift3_ge R (i.val + 1) 0 (by omega)).trans (le_max_left ..)) (by omega))
      have hm1 : M0 (i.val + 1) ∈ Earlier (rk (.p1, i)) :=
        hasM0 (i.val + 1) _ (rank_add (le_max_left ..) (by omega))
      have hm2 : M0 (i.val + 2) ∈ Earlier (rk (.p1, i)) :=
        hasM0 (i.val + 2) _ (rank_add (le_max_right ..) (by omega))
      exact pivotG hx1 hm1 hm2 (Or.inl (hu (ix hk (i.val + 2)))) (c1 (ix hk i))
    | s1 =>
      have hx0 : x (ix hk i.val) ∈ Earlier (rk (.s1, i)) :=
        hasX i.val _ (rank_add (le_max_left ..) (by omega))
      have hp1 : P1 i.val ∈ Earlier (rk (.s1, i)) :=
        hasP1 i.val _ (rank_add (le_max_right ..) (by omega))
      have he : S1 i.val = xo (x (ix hk i.val)) (P1 i.val) := by
        funext b; exact step1_eq_xor_pivot1
      rw [show F (.s1, i) = S1 i.val from rfl, he]
      exact xorG hx0 hp1
    | m1p =>
      have hp1 : P1 i.val ∈ Earlier (rk (.m1p, i)) :=
        hasP1 i.val _ (rank_add ((le_max_left ..).trans (le_max_left ..)) (by omega))
      have hs1 : S1 (i.val + 1) ∈ Earlier (rk (.m1p, i)) :=
        hasS1 (i.val + 1) _ (rank_add ((le_max_right ..).trans (le_max_left ..)) (by omega))
      have hs2 : S1 (i.val + 2) ∈ Earlier (rk (.m1p, i)) :=
        hasS1 (i.val + 2) _ (rank_add (le_max_right ..) (by omega))
      exact mixG hp1 hs1 hs2
    | m1 =>
      have hs (d : Nat) (hd : d ≤ 2) : S1 (i.val + d) ∈ Earlier (rk (.m1, i)) :=
        hasS1 (i.val + d) _ (rank_add (lift3_ge (rS1 R) i d hd) (by omega))
      exact mixG (hs 0 (by omega)) (hs 1 (by omega)) (hs 2 (by omega))
    | s2 =>
      have hm (d : Nat) (hd : d ≤ 2) : M1 (i.val + d) ∈ Earlier (rk (.s2, i)) :=
        hasM1 (i.val + d) _ (rank_add ((lift3_ge (rM1 R) i d hd).trans (le_max_left ..)) (by omega))
      have hx1 : x (ix hk (i.val + 1)) ∈ Earlier (rk (.s2, i)) :=
        hasX (i.val + 1) _ (rank_add (le_max_right ..) (by omega))
      exact rowG (hm 0 (by omega)) (hm 1 (by omega)) (hm 2 (by omega)) hx1 (Or.inl (hu (ix hk (i.val + 1)))) (c2 (ix hk i))
  rw [← node_cost k]
  refine relax (topological F rk (fun a => kindCost a.1) Finset.univ (fun a _ => Hb a)) le_rfl ?_ le_rfl
  rintro f (⟨i, rfl⟩ | ⟨i, rfl⟩)
  · exact ⟨(.x, i), Finset.mem_univ _, rfl⟩
  · exact ⟨(.s2, i), Finset.mem_univ _, rfl⟩

end RowCircuit25497

namespace Column25497

open BitBridge Build25497 RowCircuit25497 Word25497

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

private theorem colRoundG {k n : Nat} (hk : 0 < k) {A : Set (Sig n)}
    (w s : (Fin n → Bool) → Nat) (hw : ∀ v, w v < 2 ^ k) (hs : ∀ v, s v < 2 ^ k)
    (hW : ∀ i : Fin k, bits w i ∈ A) (hS : ∀ i : Fin k, bits s i ∈ A) (e t : Nat) :
    Build A (Set.range (fun i : Fin k => bits (fun v => updateRound k 2 e t (w v) (s v)) i)) (19 * k) := by
  let w₁ := fun v => s v ^^^ rot k 2 (s v) ^^^ rot k (k - 2) (s v)
  let F := fun i : Fin k => bits w₁ i
  have H : Build A (Set.range F) (k * 8) := finG F 8 fun i => by
    have E : F i = xo (xo (bits s i) (bits (fun v => rot k 2 (s v)) i))
        (bits (fun v => rot k (k - 2) (s v)) i) := by
      funext v; simp only [F, bits, w₁, Nat.testBit_xor, xo]
    rw [E]
    exact mixG (hS i) (rotG hk hs hS 2 i) (rotG hk hs hS (k - 2) i)
  let G := fun i : Fin k => bits (fun v => updateRound k 2 e t (w v) (s v)) i
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

private theorem colSchedule {k n : Nat} (hk : 0 < k) {A : Set (Sig n)}
    (w v : (Fin n → Bool) → Nat) (hw : ∀ x, w x < 2 ^ k) (hv : ∀ x, v x < 2 ^ k)
    (hW : ∀ i : Fin k, bits w i ∈ A) (hV : ∀ i : Fin k, bits v i ∈ A) (t : Nat) :
    Build A (Set.range (fun i : Fin k => bits (fun x => colWord k (w x) (v x) t) i)) (4 * k + 19 * k * t) := by
  induction t with
  | zero =>
    simpa [Nat.mul_comm] using (finG (fun i : Fin k => bits (fun x => colWord k (w x) (v x) 0) i) 4
      (fun i => xorBits i (rotG hk hw hW 3 i) (hV i)))
  | succ t IH =>
    have H := colRoundG hk (A := A ∪ Set.range (fun i : Fin k => bits (fun x => colWord k (w x) (v x) t) i)) w (fun x => colWord k (w x) (v x) t) hw
      (fun x => colWord_lt (hv x) t) (fun i => Or.inl (hW i)) (fun i => Or.inr ⟨i, rfl⟩)
        (3 * (t + 1) + 1) (2 + (t + 1))
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

end Column25497

namespace Slot25497

open BitBridge Sweep25497 Word25497 Build25497 RowCircuit25497 Column25497
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
private theorem bitU (k : Nat) (i : Fin k) : bits (U k) i ∈ base (k + k) :=
  Or.inl ⟨Fin.castAdd k i, funext fun v => (bit_pack (fun j : Fin k => v (Fin.castAdd k j)) i).symm⟩
private theorem bitV (k : Nat) (i : Fin k) : bits (V k) i ∈ base (k + k) :=
  Or.inl ⟨Fin.natAdd k i, funext fun v => (bit_pack (fun j : Fin k => v (Fin.natAdd k j)) i).symm⟩

private def X (k q z seed : Nat) (b : Fin (k + k) → Bool) : Nat → Bool :=
  fill (coordBit k z (U k b)) (fun j => coordBit k z (constant k 1) (j + 1))
    (fun j => coordBit k z (constant k 2) (j + 2)) q (fun i => seed.testBit (i - q))

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

private def keyBit {k : Nat} (z : Nat) (x : Nat → Bool) (u : Nat) (i : Fin k) : Bool :=
  let j := (i.val + 1) % k
  xor (x ((j + k - z % k) % k)) (u.testBit j)
private def key {k : Nat} (z : Nat) (x : Nat → Bool) (u : Nat) : Nat := tableIndex (keyBit (k := k) z x u)

private theorem key_coord {k z u : Nat} (hk : 1 < k) (_hu : u < 2 ^ k) (x : Nat → Bool) (i : Nat) :
    coordBit k z (rowWord k (key (k := k) z x u) u 0) i = x (i % k) := by
  have hpos : 0 < k := by omega
  let j := (z + i) % k
  have hj : j < k := Nat.mod_lt _ hpos
  let p : Fin k := ix hpos (j + k - 1)
  have he : (p.val + 1) % k = j := by
    change (((j + k - 1) % k) + 1) % k = j
    rw [Nat.mod_add_mod, Nat.sub_add_cancel (by omega), Nat.add_mod_right, Nat.mod_eq_of_lt hj]
  change (rot k 1 (key (k := k) z x u) ^^^ u).testBit j = _
  rw [Nat.testBit_xor, rbit hj hk (show key (k := k) z x u < 2 ^ k from pack_lt _)]
  change xor ((tableIndex (keyBit (k := k) z x u)).testBit p) (u.testBit j) = _
  rw [bit_pack]
  simp only [keyBit, he]
  have hidx : (j + k - z % k) % k = i % k := by
    have hej : j = (z + i % k) % k := (Nat.add_mod_mod ..).symm
    rw [hej, mod_inverse hpos (Nat.mod_lt _ hpos)]
  rw [hidx]
  cases x (i % k) <;> cases u.testBit j <;> rfl

private theorem key_unique {k z u w : Nat} (hk : 1 < k) (_hu : u < 2 ^ k) (hw : w < 2 ^ k)
    {x : Nat → Bool} (H : ∀ i < k, coordBit k z (rowWord k w u 0) i = x i) : key (k := k) z x u = w := by
  have hpos : 0 < k := by omega
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < k
  · let j := (i + 1) % k
    let p := (j + k - z % k) % k
    have hp : p < k := Nat.mod_lt _ hpos
    have hj : j < k := Nat.mod_lt _ hpos
    have he : (z + p) % k = j := mod_inverse' hpos hj
    have hi' : (j + k - 1) % k = i := by
      dsimp [j]
      rw [sub_cyclic (by omega) (by omega), Nat.add_sub_cancel, Nat.mod_eq_of_lt hi]
    have E := H p hp
    simp only [coordBit, he, rowWord, Nat.testBit_xor, rbit hj hk hw, hi'] at E
    rw [show (key (k := k) z x u).testBit i = keyBit z x u ⟨i, hi⟩ from bit_pack _ ⟨i, hi⟩]
    change xor (x p) (u.testBit j) = w.testBit i
    rw [← E]
    cases w.testBit i <;> cases u.testBit j <;> rfl
  · have hp := Nat.pow_le_pow_right Nat.zero_lt_two (by omega : k ≤ i)
    rw [Nat.testBit_lt_two_pow ((show key (k := k) z x u < 2 ^ k from pack_lt _).trans_le hp),
      Nat.testBit_lt_two_pow (hw.trans_le hp)]

private theorem Xperiod_eq {k q z seed : Nat} (hq : q + 8 ≤ k)
    (b : Fin (k + k) → Bool) (i : Fin k) (hi : i.val < q) :
    X k q z seed b i = pivot2 (coordBit k z (U k b)) (fun j => coordBit k z (constant k 1) (j + 1))
      (fun j => coordBit k z (constant k 2) (j + 2))
      (fun j => X k q z seed b (j % k)) i := by
  unfold X
  rw [fill_lt hi]
  apply pivot2_congr
  intro j hj hj'
  rw [Nat.mod_eq_of_lt (by omega : j < k)]

private theorem coord_shift {k z w j : Nat} : coordBit k z w (j % k) = coordBit k z w j := by
  simp only [coordBit, Nat.add_mod_mod]

private theorem const_shift {k z t d j : Nat} :
    coordBit k z (constant k t) (j % k + d) = coordBit k z (constant k t) (j + d) := by
  unfold coordBit
  rw [show z + (j % k + d) = j % k + (z + d) by omega, Nat.mod_add_mod]
  congr 2; omega

private def SKey (k q z seed : Nat) (b : Fin (k + k) → Bool) : Nat :=
  key (k := k) z (X k q z seed b) (U k b)

private def accept (k q z seed : Nat) (b : Fin (k + k) → Bool) : Bool :=
  decide (rowWord k (SKey k q z seed b) (U k b) 2 < 2 ^ (k - (k + 1) / 2)) &&
  decide (colWord k (SKey k q z seed b) (V k b) 2 < 2 ^ (k - (k + 1) / 2))

private theorem slotLogic {k q z seed w : Nat} (hk : 16 ≤ k)
    (hq : q + 8 ≤ k) (hz : 3 ≤ z) (hz' : z + 2 = k + (k - q))
    (qh : q = (k + 1) / 2) (b : Fin (k + k) → Bool) (hw : w < 2 ^ k)
    (hpass : rowWord k w (U k b) 2 < 2 ^ (k - (k + 1) / 2))
    (hseed : ∀ i, q ≤ i → i < k → seed.testBit (i - q) = coordBit k z (rowWord k w (U k b) 0) i) :
    SKey k q z seed b = w := by
  let y := coordBit k z (rowWord k w (U k b) 0)
  have hy (i : Nat) (hi : i < q) : y i = pivot2 (coordBit k z (U k b))
      (fun j => coordBit k z (constant k 1) (j + 1)) (fun j => coordBit k z (constant k 2) (j + 2)) y i := by
    apply step2_zero_iff.mp
    rw [← rowWord2_norm hk hw (U_lt k b) hz i]
    unfold coordBit
    have e : (z + (i + 2)) % k = i + (k - q) := by
      rw [show z + (i + 2) = (i + (k - q)) + k by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [e]
    exact (lt_two_pow_iff_testBit (rowWord_lt (U_lt k b) 2)).mp hpass _ (by omega) (by omega)
  have He := fill_unique hq (x := X k q z seed b) (y := y)
    (fun i hi hik => (fill_ge hi).trans (hseed i hi hik)) (fun i hi => fill_lt hi) hy
  exact key_unique (by omega) (U_lt k b) hw (fun i hi => (He i hi).symm)

private theorem slotCircuit {k q z seed : Nat} (hk : 16 ≤ k)
    (hq : q + 8 ≤ k) (hz : 3 ≤ z) :
    Build (base (k + k)) {accept k q z seed} (117 * k + 3) := by
  let A := base (k + k)
  let W := SKey k q z seed
  let x : Fin k → Sig (k + k) := fun i b => X k q z seed b i
  let u : Fin k → Sig (k + k) := fun i b => coordBit k z (U k b) i
  let c1 : Fin k → Bool := fun i => coordBit k z (constant k 1) (i.val + 1)
  let c2 : Fin k → Bool := fun i => coordBit k z (constant k 2) (i.val + 2)
  have hk0 : 0 < k := by omega
  have hx (i : Fin k) (hi : q ≤ i.val) : x i ∈ A := by
    have he : x i = (fun _ => seed.testBit (i.val - q)) := funext fun _ => fill_ge hi
    rw [he]
    cases seed.testBit (i.val - q) <;> exact Or.inr (by simp)
  have hu (i : Fin k) : u i ∈ A := bitU k (ix hk0 (z + i.val))
  have hp (i : Fin k) (hi : i.val < q) (b : Fin (k + k) → Bool) :
      x i b = pivot2 (fun j => u (ix hk0 j) b) (fun j => c1 (ix hk0 j)) (fun j => c2 (ix hk0 j))
        (fun j => x (ix hk0 j) b) i.val := by
    simpa only [x, u, c1, c2, ix, coord_shift, const_shift] using Xperiod_eq hq b i hi
  let R := Set.range x ∪ Set.range (fun i : Fin k => fun b =>
    step2 (fun j => u (ix hk0 j) b) (fun j => c1 (ix hk0 j)) (fun j => c2 (ix hk0 j))
        (fun j => x (ix hk0 j) b) i.val)
  have HR : Build A R (69 * k) := rowSweep2Schedule hk0 hq x u c1 c2 hu hx hp
  let K := Set.range (fun i : Fin k => bits W i)
  have HK : Build (A ∪ R) K (k * 4) := finG _ 4 fun i => by
    let j := (i.val + 1) % k
    let p := ix hk0 (j + k - z % k)
    let d := ix hk0 j
    have he : bits W i = xo (x p) (bits (U k) d) := by
      funext b
      change (tableIndex (keyBit z (X k q z seed b) (U k b))).testBit i = _
      rw [bit_pack]
      simp only [keyBit, xo, x, p, ix, bits, d, j, Nat.mod_mod]
    rw [he]
    exact xorG (Or.inr (Or.inl ⟨p, rfl⟩)) (Or.inl (bitU k d))
  have wlt (b : Fin (k + k) → Bool) : W b < 2 ^ k := pack_lt _
  let C := Set.range (fun i : Fin k => bits (fun b => colWord k (W b) (V k b) 2) i)
  have HC : Build (A ∪ (R ∪ K)) C (4 * k + 19 * k * 2) :=
    colSchedule hk0 W (V k) wlt (V_lt k) (fun i => Or.inr (Or.inr ⟨i, rfl⟩))
      (fun i => Or.inl (bitV k i)) 2
  let h := k - (k + 1) / 2
  let rl : Sig (k + k) := fun b => decide (rowWord k (W b) (U k b) 2 < 2 ^ h)
  let cl : Sig (k + k) := fun b => decide (colWord k (W b) (V k b) 2 < 2 ^ h)
  let E := ((R ∪ K) ∪ C)
  have hf : (fun _ => false) ∈ A := Or.inr (by simp)
  have allRow (i : Fin k) : bits (fun b => rowWord k (W b) (U k b) 2) i ∈ A ∪ E := by
    let p := ix hk0 (i.val + k - (z + 2) % k)
    have he : (z + (p.val + 2)) % k = i.val := by
      rw [show z + (p.val + 2) = (z + 2) + p.val by omega]
      exact mod_inverse' hk0 i.isLt
    apply Or.inr ∘ Or.inl ∘ Or.inl ∘ Or.inr
    refine ⟨p, ?_⟩
    funext b
    have J := rowWord2_norm hk (wlt b) (U_lt k b) hz p.val
    simp only [coordBit, he] at J
    change step2 (fun j => u (ix hk0 j) b) (fun j => c1 (ix hk0 j)) (fun j => c2 (ix hk0 j))
        (fun j => x (ix hk0 j) b) p.val = (rowWord k (W b) (U k b) 2).testBit i
    rw [J]
    have eu : (fun j => u (ix hk0 j) b) = coordBit k z (U k b) := funext fun _ => coord_shift
    have ec1 : (fun j => c1 (ix hk0 j)) = (fun j => coordBit k z (constant k 1) (j + 1)) := funext fun _ => const_shift
    have ec2 : (fun j => c2 (ix hk0 j)) = (fun j => coordBit k z (constant k 2) (j + 2)) := funext fun _ => const_shift
    have ex : (fun j => x (ix hk0 j) b) = coordBit k z (rowWord k (W b) (U k b) 0) :=
      funext fun j => (key_coord (by omega) (U_lt k b) _ j).symm
    rw [eu, ec1, ec2, ex]; rfl
  have Hrl : Build (A ∪ E) {rl} (k + 1) := thresholds h _
    (fun b => rowWord_lt (U_lt k b) 2) (fun i _ => allRow i) (Or.inl hf)
  have Hcl : Build (A ∪ (E ∪ {rl})) {cl} (k + 1) := thresholds h _
    (fun b => colWord_lt (V_lt k b) 2) (fun i _ => Or.inr (Or.inl (Or.inr ⟨i, rfl⟩))) (Or.inl hf)
  have HA : Build (A ∪ ((E ∪ {rl}) ∪ {cl})) {accept k q z seed} 1 :=
    andG (f := rl) (g := cl) (by simp) (by simp)
  refine relax (seq (seq (seq (seq (seq HR HK) HC) Hrl) Hcl) HA) le_rfl ?_ ?_
  · exact Set.subset_union_right
  · ring_nf; omega

end Slot25497

namespace Result25497

open BitBridge Sweep25497 Word25497 Build25497 Slot25497
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

private theorem any_graph {k q z : Nat} (hk : 16 ≤ k)
    (hq : q + 8 ≤ k) (hz : 3 ≤ z) (hz' : z + 2 = k + (k - q)) (qh : q = (k + 1) / 2)
    (b : Fin (k + k) → Bool) :
    (List.range (2 ^ (k - q))).any (fun s => accept k q z s b) =
    (List.range (2 ^ k)).any (fun w =>
      decide (rowWord k w (U k b) 2 < 2 ^ (k - (k + 1) / 2)) &&
      decide (colWord k w (V k b) 2 < 2 ^ (k - (k + 1) / 2))) := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, List.mem_range]
  constructor
  · rintro ⟨s, _, hs⟩
    exact ⟨SKey k q z s b, pack_lt _, hs⟩
  · rintro ⟨w, hw, hw'⟩
    let y := coordBit k z (rowWord k w (U k b) 0)
    let s := tableIndex (fun i : Fin (k - q) => y (i.val + q))
    refine ⟨s, pack_lt _, ?_⟩
    have H : SKey k q z s b = w := slotLogic hk hq hz hz' qh b hw
      (of_decide_eq_true (Bool.and_eq_true_iff.mp hw').1) fun i hi hik => by
        let j : Fin (k - q) := ⟨i - q, by omega⟩
        exact (bit_pack _ j).trans (congrArg y (Nat.sub_add_cancel hi))
    simpa only [accept, H] using hw'

private theorem solve (k : Nat) (hk : 16 ≤ k) :
    ∃ C : Circuit, FanInTwo C ∧ ReadsBack (k + k) C ∧
    C.size ≤ 2 ^ (k - (k + 1) / 2) * (130 * k) ∧
    ∀ b : Fin (k + k) → Bool, C.eval (List.ofFn b) =
      (List.range (2 ^ k)).any (fun w =>
        decide (rowWord k w (U k b) 2 < 2 ^ (k - (k + 1) / 2)) &&
        decide (colWord k w (V k b) 2 < 2 ^ (k - (k + 1) / 2))) := by
  let q := (k + 1) / 2
  let z := k + (k - q) - 2
  have hq : q + 8 ≤ k := by dsimp [q]; omega
  have hz : 3 ≤ z := by dsimp [z, q]; omega
  have hz' : z + 2 = k + (k - q) := by dsimp [z, q]; omega
  let N := 2 ^ (k - q)
  let s := 117 * k + 3
  let F := fun i : Fin N => accept k q z i.val
  let xs := (List.finRange N).map F
  have Hs : Build (base (k + k)) (Set.range F) (N * s) := finG F s (fun i => slotCircuit hk hq hz)
  let O : Sig (k + k) := fun b => xs.any (fun f => f b)
  have Ho : Build (base (k + k) ∪ Set.range F) {O} N := by
    simpa only [xs, List.length_map, List.length_finRange] using
      (anyG (A := base (k + k) ∪ Set.range F) xs
        (by intro f hf; obtain ⟨i, _, rfl⟩ := List.mem_map.mp hf; exact Or.inr ⟨i, rfl⟩)
        (Or.inl (Or.inr (by simp))))
  have H : Build (inputs (k + k)) {O} (2 + (N * s + N)) :=
    relax (seq (inputG (k + k)) (seq Hs Ho)) le_rfl
      (Set.singleton_subset_iff.mpr (Or.inr (Or.inr rfl))) le_rfl
  obtain ⟨c, hc, HS⟩ := H.run (GateBridge.start (F := id) (fun i : Fin (k + k) => fun b => b i) (by intros; rfl)) le_rfl
  clear H
  obtain ⟨C, hsize, hread, hfan, hout⟩ := GateBridge.finish HS (Or.inr (Set.mem_singleton O))
  refine ⟨C, hfan, hread, ?_, fun b => ?_⟩
  · rw [hsize, Nat.zero_add]
    have hn : 1 ≤ N := Nat.two_pow_pos _
    have hs130 : s + 3 ≤ 130 * k := by dsimp [s]; omega
    have h := Nat.mul_le_mul_left N hs130
    change c ≤ N * (130 * k)
    calc
      c ≤ 2 + (N * s + N) := hc
      _ ≤ N * (s + 3) := by
        rw [Nat.mul_add N s 3, show N * 3 = N + N + N by omega]
        omega
      _ ≤ N * (130 * k) := h
  · rw [hout]
    have eq : O b = (List.range N).any (fun seed => accept k q z seed b) := by
      apply Bool.eq_iff_iff.mpr
      simp only [O, xs, List.any_eq_true, List.mem_map, List.mem_range]
      constructor
      · rintro ⟨_, ⟨i, _, rfl⟩, hh⟩
        exact ⟨i.val, i.isLt, hh⟩
      · rintro ⟨i, hi, hh⟩
        exact ⟨F ⟨i, hi⟩, ⟨⟨i, hi⟩, List.mem_finRange _, rfl⟩, hh⟩
    exact eq.trans (any_graph hk hq hz hz' rfl b)

end Result25497

end PEqualNP.Outside.L_meta_25497_aux

open PEqualNP.Outside.L_meta_25497_aux.BitBridge PEqualNP.Outside.L_meta_25497_aux.Word25497
open PEqualNP.Outside.L_meta_25497_aux.Slot25497 PEqualNP.Outside.L_meta_25497_aux.Result25497

theorem PEqualNP.Outside.L_meta_25497 : ∀ k : Nat, 16 ≤ k →
  let rot := fun (s word : Nat) =>
    ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k
  let step := fun (word : Nat) =>
    (List.range k).foldl (fun acc i =>
      acc ||| ((xor (word.testBit i)
        (!(word.testBit ((i + 1) % k)) && word.testBit ((i + 2) % k))).toNat <<< i)) 0
  let constant := fun (j : Nat) => 3 ^ (k + j) % 2 ^ k
  let rowMix := fun (x : Nat) => step (x ^^^ rot 1 x ^^^ rot (k - 1) x)
  let colMix := fun (z : Nat) => step (z ^^^ rot 2 z ^^^ rot (k - 2) z)
  let first := fun (rowKey rowName : Nat) =>
    let x0 := rot 1 rowKey ^^^ rowName
    let x1 := rowMix x0 ^^^ rot 0 rowKey ^^^ constant 1
    rowMix x1 ^^^ rot 2 rowKey ^^^ constant 2
  let second := fun (colKey colName : Nat) =>
    let z0 := rot 3 colKey ^^^ colName
    let z1 := colMix z0 ^^^ rot 4 colKey ^^^ constant 3
    colMix z1 ^^^ rot 7 colKey ^^^ constant 4
  let slots := 2 ^ (k - (k + 1) / 2)
  let graph : Fin (2 ^ k) → Fin (2 ^ k) → Bool := fun row col =>
    (List.range (2 ^ k)).any (fun w =>
      decide (first w row.val < slots) && decide (second w col.val < slots))
  ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (k + k) C ∧
    C.size ≤ slots * (130 * k) ∧
    ∀ bits : Fin (k + k) → Bool,
      C.eval (List.ofFn bits) = PEqualNP.Represents.adjFun (k := k) (l := k) graph bits := by
  intro k hk
  dsimp only
  obtain ⟨C, hFan, hRead, hSize, hEval⟩ := solve k hk
  refine ⟨C, hFan, hRead, hSize, fun b => ?_⟩
  rw [hEval]
  unfold PEqualNP.Represents.adjFun
  dsimp only
  simp only [← wordStep_eq]
  change _ = (List.range (2 ^ k)).any (fun w =>
    decide (rowWord k w ((U k b) % 2 ^ k) 2 < 2 ^ (k - (k + 1) / 2)) &&
    decide (colWord k w ((V k b) % 2 ^ k) 2 < 2 ^ (k - (k + 1) / 2)))
  simp only [Nat.mod_eq_of_lt (U_lt k b), Nat.mod_eq_of_lt (V_lt k b)]
