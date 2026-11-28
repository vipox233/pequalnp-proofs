import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_32588_aux

open Finset
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents

abbrev Legal (N : ℕ) (C : Circuit) : Prop :=
  ReadsBack (N + N) C ∧ C.output < N + N + C.size ∧
  ∀ gate ∈ C.gates, gate.inputs.length ≤ 2 ∧
    (gate.op = .and ∨ gate.op = .or ∨ (gate.op = .not ∧ gate.inputs.length = 1))

def wiresStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def wiresUpTo (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl wiresStep x

lemma wiresUpTo_nil (x : List Bool) : wiresUpTo [] x = x := rfl

lemma wiresUpTo_concat (gs : List Gate) (g : Gate) (x : List Bool) :
    wiresUpTo (gs ++ [g]) x = wiresStep (wiresUpTo gs x) g := by
  simp [wiresUpTo, List.foldl_append]

lemma wiresUpTo_length (gs : List Gate) (x : List Bool) :
    (wiresUpTo gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [wiresUpTo]
  | append_singleton gs g ih =>
    rw [wiresUpTo_concat, wiresStep, List.length_append, List.length_singleton, ih,
      List.length_append, List.length_singleton]
    omega

lemma getD_append_lt {α : Type*} (l₁ l₂ : List α) (i : ℕ) (d : α) (h : i < l₁.length) :
    (l₁ ++ l₂).getD i d = l₁.getD i d := by
  simp [List.getD, List.getElem?_append_left h]

lemma getD_append_eq {α : Type*} (l : List α) (a d : α) :
    (l ++ [a]).getD l.length d = a := by
  simp [List.getD]

lemma wiresUpTo_take_getD (gs : List Gate) (x : List Bool) (k w : ℕ)
    (hk : k ≤ gs.length) (hw : w < x.length + k) :
    (wiresUpTo gs x).getD w false = (wiresUpTo (gs.take k) x).getD w false := by
  induction gs using List.reverseRecOn generalizing k with
  | nil => simp at hk; subst hk; rfl
  | append_singleton gs g ih =>
    by_cases hle : k ≤ gs.length
    · rw [List.take_append_of_le_length hle, wiresUpTo_concat, wiresStep,
        getD_append_lt _ _ _ _ (by rw [wiresUpTo_length]; omega)]
      exact ih k hle hw
    · have hk_eq : k = gs.length + 1 := by simp at hk; omega
      subst hk_eq
      rw [List.take_of_length_le (by simp)]

lemma wires_getD_input (C : Circuit) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (C.wires x).getD i false = x.getD i false := by
  have h := wiresUpTo_take_getD C.gates x 0 i (Nat.zero_le _) (by omega)
  change (wiresUpTo C.gates x).getD i false = x.getD i false
  simpa [wiresUpTo] using h

lemma wires_getD_gate (C : Circuit) (x : List Bool) (j : ℕ)
    (hRB : ReadsBack x.length C) (hj : j < C.gates.length) :
    (C.wires x).getD (x.length + j) false =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => (C.wires x).getD i false) := by
  have h1 := wiresUpTo_take_getD C.gates x (j + 1) (x.length + j) (by omega) (by omega)
  have htake : C.gates.take (j + 1) = C.gates.take j ++ [C.gates[j]] := by
    rw [List.take_succ_eq_append_getElem hj]
  have hgate : gateAt C j = C.gates[j] := by
    simp [gateAt, List.getD, hj]
  change (wiresUpTo C.gates x).getD (x.length + j) false = _
  rw [h1, htake, wiresUpTo_concat, wiresStep]
  have hlen : (wiresUpTo (C.gates.take j) x).length = x.length + j := by
    rw [wiresUpTo_length, List.length_take, Nat.min_eq_left (by omega)]
  rw [← hlen, getD_append_eq, hgate]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hi' : i < x.length + j := hRB j hj i (by rwa [hgate])
  exact (wiresUpTo_take_getD C.gates x j i (by omega) hi').symm

def isNot : GateOp → Bool
  | .not => true
  | _ => false

def frontierAux (n : ℕ) (C : Circuit) : ℕ → Finset ℕ × ℕ × Bool → Finset ℕ × ℕ × Bool
  | 0, st => st
  | k + 1, (F, e, hn) =>
    if n + k ∈ F then
      let g := gateAt C k
      frontierAux n C k ((F.erase (n + k)) ∪ g.inputs.toFinset, e + 1, hn || isNot g.op)
    else
      frontierAux n C k (F, e, hn)

lemma frontierAux_inv (n : ℕ) (C : Circuit) (hRB : ReadsBack n C)
    (hG : ∀ gate ∈ C.gates, gate.inputs.length ≤ 2 ∧
      (gate.op = .and ∨ gate.op = .or ∨ (gate.op = .not ∧ gate.inputs.length = 1)))
    (m : ℕ) (hm : m ≤ C.gates.length) (F : Finset ℕ) (e : ℕ) (hn : Bool)
    (hF : ∀ w ∈ F, w < n + m)
    (hcard : F.card + (if hn then 1 else 0) ≤ e + 1) :
    let res := frontierAux n C m (F, e, hn)
    (∀ w ∈ res.1, w < n) ∧
    res.1.card + (if res.2.2 then 1 else 0) ≤ res.2.1 + 1 ∧
    res.2.1 ≤ e + m := by
  induction m generalizing F e hn with
  | zero =>
    simp only [frontierAux]
    refine ⟨by simpa using hF, hcard, by omega⟩
  | succ k ih =>
    by_cases hmem : n + k ∈ F
    · simp only [frontierAux, hmem, ↓reduceIte]
      have hk : k < C.gates.length := by omega
      have hg_mem : gateAt C k ∈ C.gates := by
        simp [gateAt, List.getD, hk]
      have hg := hG (gateAt C k) hg_mem
      have hF' : ∀ w ∈ (F.erase (n + k)) ∪ (gateAt C k).inputs.toFinset, w < n + k := by
        intro w hw
        rcases Finset.mem_union.mp hw with hw1 | hw2
        · have hwF := Finset.mem_of_mem_erase hw1
          have hne := Finset.ne_of_mem_erase hw1
          have := hF w hwF
          omega
        · exact hRB k hk w (List.mem_toFinset.mp hw2)
      have herase : (F.erase (n + k)).card + 1 = F.card := Finset.card_erase_add_one hmem
      have hunion : ((F.erase (n + k)) ∪ (gateAt C k).inputs.toFinset).card ≤
          (F.erase (n + k)).card + (gateAt C k).inputs.toFinset.card := Finset.card_union_le _ _
      have htofin : (gateAt C k).inputs.toFinset.card ≤ (gateAt C k).inputs.length :=
        List.toFinset_card_le _
      have hcard' : ((F.erase (n + k)) ∪ (gateAt C k).inputs.toFinset).card +
          (if hn || isNot (gateAt C k).op then 1 else 0) ≤ (e + 1) + 1 := by
        rcases hg.2 with hand | hor | ⟨hnot, hlen1⟩
        · simp only [hand, isNot, Bool.or_false]
          have := hg.1
          omega
        · simp only [hor, isNot, Bool.or_false]
          have := hg.1
          omega
        · simp only [hnot, isNot, Bool.or_true]
          cases hn <;> simp at hcard ⊢ <;> omega
      have hrec := ih (by omega) _ (e + 1) (hn || isNot (gateAt C k).op) hF' hcard'
      exact ⟨hrec.1, hrec.2.1, by omega⟩
    · simp only [frontierAux, hmem, ↓reduceIte]
      have hF' : ∀ w ∈ F, w < n + k := by
        intro w hw
        have hlt := hF w hw
        have hne : w ≠ n + k := fun heq => hmem (heq ▸ hw)
        omega
      have hrec := ih (by omega) F e hn hF' hcard
      exact ⟨hrec.1, hrec.2.1, by omega⟩

lemma frontierAux_agree (n : ℕ) (C : Circuit) (hRB : ReadsBack n C)
    (x y : List Bool) (hx : x.length = n) (hy : y.length = n)
    (m : ℕ) (hm : m ≤ C.gates.length) (F : Finset ℕ) (e : ℕ) (hn : Bool)
    (hF : ∀ w ∈ F, w < n + m)
    (hagree : ∀ w ∈ (frontierAux n C m (F, e, hn)).1, x.getD w false = y.getD w false) :
    ∀ w ∈ F, (C.wires x).getD w false = (C.wires y).getD w false := by
  induction m generalizing F e hn with
  | zero =>
    intro w hw
    have hw_lt : w < n := by simpa using hF w hw
    rw [wires_getD_input C x w (by omega), wires_getD_input C y w (by omega)]
    exact hagree w hw
  | succ k ih =>
    simp only [frontierAux] at hagree
    split_ifs at hagree with hmem
    · have hk : k < C.gates.length := by omega
      have hF' : ∀ w ∈ (F.erase (n + k)) ∪ (gateAt C k).inputs.toFinset, w < n + k := by
        intro w hw
        rcases Finset.mem_union.mp hw with hw1 | hw2
        · have := hF w (Finset.mem_of_mem_erase hw1)
          have := Finset.ne_of_mem_erase hw1
          omega
        · exact hRB k hk w (List.mem_toFinset.mp hw2)
      have ih_res := ih (by omega) _ (e + 1) (hn || isNot (gateAt C k).op) hF' hagree
      intro w hw
      by_cases hwk : w = n + k
      · subst hwk
        have hgx := wires_getD_gate C x k (hx ▸ hRB) hk
        have hgy := wires_getD_gate C y k (hy ▸ hRB) hk
        rw [hx] at hgx; rw [hy] at hgy
        rw [hgx, hgy]
        congr 1
        apply List.map_congr_left
        intro i hi
        exact ih_res i (Finset.mem_union_right _ (List.mem_toFinset.mpr hi))
      · exact ih_res w (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hwk, hw⟩))
    · have hF' : ∀ w ∈ F, w < n + k := by
        intro w hw
        have := hF w hw
        have hne : w ≠ n + k := fun heq => hmem (heq ▸ hw)
        omega
      exact ih (by omega) F e hn hF' hagree

lemma oneEach_length {N : ℕ} (x y : Fin N) : (oneEach x y).length = N + N := by
  simp [oneEach]

lemma oneEach_getD_left {N : ℕ} (x y : Fin N) (i : ℕ) (hi : i < N) :
    (oneEach x y).getD i false = decide (i = x.val) := by
  unfold oneEach
  rw [getD_append_lt _ _ _ _ (by simp [hi])]
  simp [List.getD, hi, Fin.ext_iff]

lemma oneEach_getD_right {N : ℕ} (x y : Fin N) (j : ℕ) (hj : j < N) :
    (oneEach x y).getD (N + j) false = decide (j = y.val) := by
  unfold oneEach
  simp [List.getD, List.getElem?_append_right, hj, Fin.ext_iff]

def targetI (N t u : ℕ) (x y : Fin N) : Bool :=
  decide ((y.val + N - x.val + N - u % N) % N < t)

lemma card_targetI_col {N t : ℕ} (ht : t ≤ N) (u : ℕ) (x : Fin N) :
    ((Finset.univ : Finset (Fin N)).filter (fun y => targetI N t u x y = true)).card = t := by
  have hN : 0 < N := by exact Fin.pos x
  let f : Fin N → Fin N := fun y => ⟨(y.val + N - x.val + N - u % N) % N, Nat.mod_lt _ hN⟩
  have hbij : Function.Bijective f := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨?_, rfl⟩
    intro y₁ y₂ h
    have hv := congrArg Fin.val h
    simp only [f] at hv
    have hx := x.isLt; have hu := Nat.mod_lt u hN
    have hy1 := y₁.isLt; have hy2 := y₂.isLt
    have h1 : (y₁.val + (N - x.val) + (N - u % N)) % N = (y₂.val + (N - x.val) + (N - u % N)) % N := by
      have e1 : y₁.val + N - x.val + N - u % N = y₁.val + (N - x.val) + (N - u % N) := by omega
      have e2 : y₂.val + N - x.val + N - u % N = y₂.val + (N - x.val) + (N - u % N) := by omega
      rw [← e1, ← e2]; exact hv
    have h2 : (y₁.val + ((N - x.val) + (N - u % N))) % N =
        (y₂.val + ((N - x.val) + (N - u % N))) % N := by
      simpa [Nat.add_assoc] using h1
    apply Fin.ext
    have h3 : (y₁.val + ((N - x.val) + (N - u % N))) % N =
        (y₁.val + ((N - x.val) + (N - u % N)) % N) % N := by
      rw [Nat.add_mod, Nat.add_mod y₁.val, Nat.mod_mod]
    have h4 : (y₂.val + ((N - x.val) + (N - u % N))) % N =
        (y₂.val + ((N - x.val) + (N - u % N)) % N) % N := by
      rw [Nat.add_mod, Nat.add_mod y₂.val, Nat.mod_mod]
    set c := ((N - x.val) + (N - u % N)) % N
    have hc : c < N := Nat.mod_lt _ hN
    rw [h3, h4] at h2
    by_cases h1c : y₁.val + c < N <;> by_cases h2c : y₂.val + c < N
    · rw [Nat.mod_eq_of_lt h1c, Nat.mod_eq_of_lt h2c] at h2; omega
    · rw [Nat.mod_eq_of_lt h1c, Nat.mod_eq_sub_mod (by omega),
        Nat.mod_eq_of_lt (by omega)] at h2; omega
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt h2c] at h2; omega
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at h2; omega
  let e := Equiv.ofBijective f hbij
  have hcard : ((Finset.univ : Finset (Fin N)).filter (fun y => (f y).val < t)).card =
      ((Finset.univ : Finset (Fin N)).filter (fun z : Fin N => z.val < t)).card := by
    refine Finset.card_bij (fun y _ => f y) (fun y hy => by simpa using hy)
      (fun a _ b _ h => hbij.1 h) (fun z hz => ?_)
    obtain ⟨y, hy⟩ := hbij.2 z
    exact ⟨y, by simpa [hy] using hz, hy⟩
  have hlt : ((Finset.univ : Finset (Fin N)).filter (fun z : Fin N => z.val < t)).card = t := by
    refine (Finset.card_bij (fun z _ => z.val) (fun z hz => by simp at hz ⊢; exact hz)
      (fun a _ b _ h => Fin.ext h) (fun k hk => ?_)).trans (Finset.card_range t)
    simp at hk
    exact ⟨⟨k, by omega⟩, by simp [hk], rfl⟩
  simpa [targetI, f] using hcard.trans hlt

lemma card_targetI_row {N t : ℕ} (ht : t ≤ N) (u : ℕ) (y : Fin N) :
    ((Finset.univ : Finset (Fin N)).filter (fun x => targetI N t u x y = true)).card = t := by
  have hN : 0 < N := Fin.pos y
  let f : Fin N → Fin N := fun x => ⟨(y.val + N - x.val + N - u % N) % N, Nat.mod_lt _ hN⟩
  have hbij : Function.Bijective f := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨?_, rfl⟩
    intro x₁ x₂ h
    have hv := congrArg Fin.val h
    simp only [f] at hv
    have hy := y.isLt; have hu := Nat.mod_lt u hN
    have hx1 := x₁.isLt; have hx2 := x₂.isLt
    have h1 : ((N - x₁.val) + (y.val + (N - u % N))) % N =
        ((N - x₂.val) + (y.val + (N - u % N))) % N := by
      have e1 : y.val + N - x₁.val + N - u % N = (N - x₁.val) + (y.val + (N - u % N)) := by omega
      have e2 : y.val + N - x₂.val + N - u % N = (N - x₂.val) + (y.val + (N - u % N)) := by omega
      rw [← e1, ← e2]; exact hv
    set c := (y.val + (N - u % N)) % N
    have hc : c < N := Nat.mod_lt _ hN
    have h3 : ((N - x₁.val) + (y.val + (N - u % N))) % N = ((N - x₁.val) + c) % N := by
      rw [Nat.add_mod, Nat.add_mod (N - x₁.val), Nat.mod_mod]
    have h4 : ((N - x₂.val) + (y.val + (N - u % N))) % N = ((N - x₂.val) + c) % N := by
      rw [Nat.add_mod, Nat.add_mod (N - x₂.val), Nat.mod_mod]
    rw [h3, h4] at h1
    apply Fin.ext
    by_cases h1c : N - x₁.val + c < N <;> by_cases h2c : N - x₂.val + c < N
    · rw [Nat.mod_eq_of_lt h1c, Nat.mod_eq_of_lt h2c] at h1; omega
    · have hlt2 : N - x₂.val + c - N < N := by omega
      rw [Nat.mod_eq_of_lt h1c, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt hlt2] at h1
      omega
    · have hlt1 : N - x₁.val + c - N < N := by omega
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt hlt1, Nat.mod_eq_of_lt h2c] at h1
      omega
    · have hlt1 : N - x₁.val + c - N < N := by omega
      have hlt2 : N - x₂.val + c - N < N := by omega
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt hlt1,
        Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt hlt2] at h1
      omega
  have hcard : ((Finset.univ : Finset (Fin N)).filter (fun x => (f x).val < t)).card =
      ((Finset.univ : Finset (Fin N)).filter (fun z : Fin N => z.val < t)).card := by
    refine Finset.card_bij (fun x _ => f x) (fun x hx => by simpa using hx)
      (fun a _ b _ h => hbij.1 h) (fun z hz => ?_)
    obtain ⟨x, hx⟩ := hbij.2 z
    exact ⟨x, by simpa [hx] using hz, hx⟩
  have hlt : ((Finset.univ : Finset (Fin N)).filter (fun z : Fin N => z.val < t)).card = t := by
    refine (Finset.card_bij (fun z _ => z.val) (fun z hz => by simp at hz ⊢; exact hz)
      (fun a _ b _ h => Fin.ext h) (fun k hk => ?_)).trans (Finset.card_range t)
    simp at hk
    exact ⟨⟨k, by omega⟩, by simp [hk], rfl⟩
  simpa [targetI, f] using hcard.trans hlt

lemma card_targetI_u {N t : ℕ} (ht : t ≤ N) (x y : Fin N) :
    ((Finset.univ : Finset (Fin N)).filter (fun u : Fin N => targetI N t u.val x y = true)).card = t := by
  have hN : 0 < N := Fin.pos x
  have heq : (Finset.univ : Finset (Fin N)).filter (fun u : Fin N => targetI N t u.val x y = true) =
      (Finset.univ : Finset (Fin N)).filter (fun u : Fin N => targetI N t x.val u y = true) := by
    apply Finset.filter_congr
    intro u _
    simp only [targetI, Nat.mod_eq_of_lt u.isLt, Nat.mod_eq_of_lt x.isLt]
    have h1 : y.val + N - x.val + N - u.val = y.val + N - u.val + N - x.val := by
      have := x.isLt; have := u.isLt; omega
    rw [h1]
  rw [heq]
  exact card_targetI_row ht x.val y

lemma card_targetI_all {N t : ℕ} (ht : t ≤ N) (u : ℕ) :
    ((Finset.univ : Finset (Fin N × Fin N)).filter (fun z => targetI N t u z.1 z.2 = true)).card =
      N * t := by
  rw [Finset.card_filter, Fintype.sum_prod_type]
  have hinner : ∀ x : Fin N, ∑ y : Fin N, (if targetI N t u x y = true then 1 else 0) = t := by
    intro x
    rw [← Finset.card_filter]
    exact card_targetI_col ht u x
  simp [hinner]

lemma loss_add_two_overlap {N t : ℕ} (ht : t ≤ N) (P : Fin N × Fin N → Bool) (u : ℕ) :
    ((Finset.univ : Finset (Fin N × Fin N)).filter (fun z => P z ≠ targetI N t u z.1 z.2)).card +
      2 * ((Finset.univ : Finset (Fin N × Fin N)).filter
        (fun z => P z = true ∧ targetI N t u z.1 z.2 = true)).card =
    ((Finset.univ : Finset (Fin N × Fin N)).filter (fun z => P z = true)).card + N * t := by
  rw [← card_targetI_all ht u]
  simp only [Finset.card_filter, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro z _
  cases P z <;> cases targetI N t u z.1 z.2 <;> simp

lemma sum_overlap_eq {N t : ℕ} (ht : t ≤ N) (P : Fin N × Fin N → Bool) :
    ∑ u : Fin N, ((Finset.univ : Finset (Fin N × Fin N)).filter
      (fun z => P z = true ∧ targetI N t u.val z.1 z.2 = true)).card =
    t * ((Finset.univ : Finset (Fin N × Fin N)).filter (fun z => P z = true)).card := by
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  by_cases hp : P z = true
  · simp only [hp, true_and, ↓reduceIte, mul_one]
    rw [← Finset.card_filter]
    exact card_targetI_u ht z.1 z.2
  · simp [hp]

lemma sum_loss_eq {N t : ℕ} (hNt : N < 2 * t) (ht : t ≤ N) (P : Fin N × Fin N → Bool) :
    ∑ u : Fin N, ((Finset.univ : Finset (Fin N × Fin N)).filter
      (fun z => P z ≠ targetI N t u.val z.1 z.2)).card +
      (2 * t - N) * ((Finset.univ : Finset (Fin N × Fin N)).filter (fun z => P z = true)).card =
    N * (N * t) := by
  have hsum : ∑ u : Fin N, (((Finset.univ : Finset (Fin N × Fin N)).filter
        (fun z => P z ≠ targetI N t u.val z.1 z.2)).card +
      2 * ((Finset.univ : Finset (Fin N × Fin N)).filter
        (fun z => P z = true ∧ targetI N t u.val z.1 z.2 = true)).card) =
      ∑ _u : Fin N, (((Finset.univ : Finset (Fin N × Fin N)).filter (fun z => P z = true)).card +
        N * t) := by
    apply Finset.sum_congr rfl
    intro u _
    exact loss_add_two_overlap ht P u.val
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_overlap_eq ht P,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum
  set a := ((Finset.univ : Finset (Fin N × Fin N)).filter (fun z => P z = true)).card
  have h1 : 2 * (t * a) = (2 * t - N) * a + N * a := by
    rw [← Nat.add_mul, Nat.sub_add_cancel (by omega), Nat.mul_assoc]
  have h2 : N * (a + N * t) = N * a + N * (N * t) := by ring
  omega

def orChain (n : ℕ) (w0 : ℕ) (ws : List ℕ) : Circuit :=
  { gates := (List.range ws.length).zipWith
      (fun k w => ⟨GateOp.or, [if k = 0 then w0 else n + k - 1, w]⟩) ws
    output := if ws.length = 0 then w0 else n + ws.length - 1 }

lemma orChain_size (n w0 : ℕ) (ws : List ℕ) : (orChain n w0 ws).size = ws.length := by
  simp [Circuit.size, orChain]

lemma orChain_readsBack (n w0 : ℕ) (ws : List ℕ) (hw0 : w0 < n) (hws : ∀ w ∈ ws, w < n) :
    ReadsBack n (orChain n w0 ws) := by
  intro j hj i hi
  simp only [orChain, List.length_zipWith, List.length_range, min_self] at hj
  have hgate : gateAt (orChain n w0 ws) j =
      ⟨GateOp.or, [if j = 0 then w0 else n + j - 1, ws[j]]⟩ := by
    simp [gateAt, orChain, List.getD, hj]
  rw [hgate] at hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl
  · split_ifs <;> omega
  · have := hws ws[j] (List.getElem_mem hj)
    omega

lemma orChain_legal (N w0 : ℕ) (ws : List ℕ) (hw0 : w0 < N + N)
    (hws : ∀ w ∈ ws, w < N + N) : Legal N (orChain (N + N) w0 ws) := by
  refine ⟨orChain_readsBack (N + N) w0 ws hw0 hws, ?_, ?_⟩
  · rw [orChain_size]
    simp only [orChain]
    split_ifs <;> omega
  · intro gate hgate
    rw [List.mem_iff_getElem] at hgate
    rcases hgate with ⟨j, hj, rfl⟩
    simp [orChain]

lemma orChain_eval (n w0 : ℕ) (ws : List ℕ) (hw0 : w0 < n) (hws : ∀ w ∈ ws, w < n)
    (x : List Bool) (hx : x.length = n) :
    (orChain n w0 ws).eval x = (w0 :: ws).any (fun w => x.getD w false) := by
  have hRB := orChain_readsBack n w0 ws hw0 hws
  have hwire : ∀ j < ws.length,
      ((orChain n w0 ws).wires x).getD (n + j) false =
        (w0 :: ws.take (j + 1)).any (fun w => x.getD w false) := by
    intro j
    induction j with
    | zero =>
      intro hj
      have hgt := wires_getD_gate (orChain n w0 ws) x 0 (hx ▸ hRB) (by simp [orChain, hj])
      rw [hx] at hgt
      have hga : gateAt (orChain n w0 ws) 0 = ⟨GateOp.or, [w0, ws[0]]⟩ := by
        simp [gateAt, orChain, List.getD, hj]
      rw [hgt, hga]
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq,
        Bool.or_false]
      rw [wires_getD_input _ _ w0 (by omega),
        wires_getD_input _ _ ws[0] (by have := hws ws[0] (List.getElem_mem hj); omega)]
      rw [List.take_succ_eq_append_getElem hj]
      simp
    | succ k ih =>
      intro hj
      have hgt := wires_getD_gate (orChain n w0 ws) x (k + 1) (hx ▸ hRB)
        (by simp [orChain, hj])
      rw [hx] at hgt
      have hga : gateAt (orChain n w0 ws) (k + 1) = ⟨GateOp.or, [n + k, ws[k + 1]]⟩ := by
        simp [gateAt, orChain, List.getD, hj]
      rw [hgt, hga]
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq,
        Bool.or_false]
      rw [ih (by omega),
        wires_getD_input _ _ ws[k + 1] (by have := hws ws[k + 1] (List.getElem_mem hj); omega)]
      rw [List.take_succ_eq_append_getElem hj]
      simp only [List.any_cons, List.any_append, List.any_nil, Bool.or_false]
      exact Bool.or_assoc _ _ _
  cases hlen : ws.length with
  | zero =>
    have hws_nil : ws = [] := List.eq_nil_of_length_eq_zero hlen
    subst hws_nil
    simp only [Circuit.eval, orChain, List.length_nil, ↓reduceIte, List.any_cons, List.any_nil,
      Bool.or_false]
    exact wires_getD_input _ _ w0 (by omega)
  | succ m =>
    have h1 := hwire m (by omega)
    rw [show m + 1 = ws.length from hlen.symm, List.take_length] at h1
    simpa [Circuit.eval, orChain, hlen] using h1

lemma struct_eq {N : ℕ} (hN : 5 < N) (C : Circuit) (hleg : Legal N C) (hsize : C.size ≤ 2)
    (harea : ((Finset.univ : Finset (Fin N × Fin N)).filter
      (fun z => C.eval (oneEach z.1 z.2) = true)).card = 3 * N - 2) :
    ∃ SR SC : Finset (Fin N), ((SR.card = 2 ∧ SC.card = 1) ∨ (SR.card = 1 ∧ SC.card = 2)) ∧
      ∀ x y : Fin N, C.eval (oneEach x y) = true ↔ (x ∈ SR ∨ y ∈ SC) := by
  set tbl : Fin N → Fin N → Bool := fun x y => C.eval (oneEach x y)
  set T : Finset (Fin N × Fin N) := Finset.univ.filter (fun z => tbl z.1 z.2 = true)
  change T.card = 3 * N - 2 at harea
  set res := frontierAux (N + N) C C.gates.length ({C.output}, 0, false)
  have hinv := frontierAux_inv (N + N) C hleg.1 hleg.2.2 C.gates.length (le_refl _)
    {C.output} 0 false (by intro w hw; simp at hw; subst hw; exact hleg.2.1) (by simp)
  set F0 : Finset ℕ := res.1
  set SR : Finset (Fin N) := Finset.univ.filter (fun x : Fin N => x.val ∈ F0)
  set SC : Finset (Fin N) := Finset.univ.filter (fun y : Fin N => N + y.val ∈ F0)
  have hSR_SC_card : SR.card + SC.card = F0.card := by
    have hdisj : Disjoint (SR.image Fin.val) (SC.image (fun y : Fin N => N + y.val)) := by
      rw [Finset.disjoint_left]
      intro w hw1 hw2
      rcases Finset.mem_image.mp hw1 with ⟨x, _, rfl⟩
      rcases Finset.mem_image.mp hw2 with ⟨y, _, hy⟩
      omega
    have heq : SR.image Fin.val ∪ SC.image (fun y : Fin N => N + y.val) = F0 := by
      ext w
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
        true_and, SR, SC]
      constructor
      · rintro (⟨x, hx, rfl⟩ | ⟨y, hy, rfl⟩) <;> assumption
      · intro hw
        have hwlt := hinv.1 w hw
        by_cases h : w < N
        · left; exact ⟨⟨w, h⟩, hw, rfl⟩
        · right
          have hw' : N + (w - N) = w := by omega
          exact ⟨⟨w - N, by omega⟩, by rwa [hw'], hw'⟩
    rw [← heq, Finset.card_union_of_disjoint hdisj,
      Finset.card_image_of_injective _ Fin.val_injective,
      Finset.card_image_of_injective _ (fun a b h => Fin.ext (by omega))]
  have hab_le : SR.card + SC.card ≤ 3 := by
    have h1 : F0.card + (if res.2.2 then 1 else 0) ≤ res.2.1 + 1 := hinv.2.1
    have h2 : res.2.1 ≤ 0 + C.gates.length := hinv.2.2
    have h3 : C.gates.length ≤ 2 := hsize
    have h4 : F0.card ≤ F0.card + (if res.2.2 then 1 else 0) := Nat.le_add_right _ _
    omega
  have hSR_lt : SR.card < N := by omega
  have hSC_lt : SC.card < N := by omega
  obtain ⟨x0, hx0⟩ : ∃ x : Fin N, x ∉ SR := by
    by_contra hall; push_neg at hall
    have : SR = Finset.univ := Finset.eq_univ_iff_forall.mpr hall
    rw [this, Finset.card_univ, Fintype.card_fin] at hSR_lt; omega
  obtain ⟨y0, hy0⟩ : ∃ y : Fin N, y ∉ SC := by
    by_contra hall; push_neg at hall
    have : SC = Finset.univ := Finset.eq_univ_iff_forall.mpr hall
    rw [this, Finset.card_univ, Fintype.card_fin] at hSC_lt; omega
  have h_agree : ∀ x₁ y₁ x₂ y₂ : Fin N,
      (∀ x ∈ SR, (x = x₁ ↔ x = x₂)) → (∀ y ∈ SC, (y = y₁ ↔ y = y₂)) →
      tbl x₁ y₁ = tbl x₂ y₂ := by
    intro x₁ y₁ x₂ y₂ hxr hyc
    apply frontierAux_agree (N + N) C hleg.1 (oneEach x₁ y₁) (oneEach x₂ y₂)
      (oneEach_length x₁ y₁) (oneEach_length x₂ y₂) C.gates.length (le_refl _)
      {C.output} 0 false (by intro w hw; simp at hw; subst hw; exact hleg.2.1)
    · intro w hw
      have hwlt := hinv.1 w hw
      by_cases h : w < N
      · rw [oneEach_getD_left x₁ y₁ w h, oneEach_getD_left x₂ y₂ w h]
        have hmem : (⟨w, h⟩ : Fin N) ∈ SR := by simp [SR, F0, res, hw]
        have hiff := hxr ⟨w, h⟩ hmem
        simp [Fin.ext_iff] at hiff
        simp [hiff]
      · have hj : w - N < N := by omega
        have hw_eq : w = N + (w - N) := by omega
        rw [hw_eq, oneEach_getD_right x₁ y₁ (w - N) hj, oneEach_getD_right x₂ y₂ (w - N) hj]
        have hmem : (⟨w - N, hj⟩ : Fin N) ∈ SC := by simp [SC, F0, res, ← hw_eq, hw]
        have hiff := hyc ⟨w - N, hj⟩ hmem
        simp [Fin.ext_iff] at hiff
        simp [hiff]
    · simp
  have hout_false : ∀ x y : Fin N, x ∉ SR → y ∉ SC → tbl x y = false := by
    have hconst : ∀ x y : Fin N, x ∉ SR → y ∉ SC → tbl x y = tbl x0 y0 := by
      intro x y hx hy
      apply h_agree x y x0 y0
      · intro a ha; constructor <;> intro h <;> subst h <;> contradiction
      · intro b hb; constructor <;> intro h <;> subst h <;> contradiction
    cases h0 : tbl x0 y0
    · intro x y hx hy; rw [hconst x y hx hy, h0]
    · exfalso
      have hsub : SRᶜ ×ˢ SCᶜ ⊆ T := by
        intro z hz
        simp only [Finset.mem_product, Finset.mem_compl] at hz
        simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [hconst z.1 z.2 hz.1 hz.2, h0]
      have hcard_le := Finset.card_le_card hsub
      rw [Finset.card_product, Finset.card_compl, Finset.card_compl, Fintype.card_fin] at hcard_le
      have h1 : (N - SR.card) * (N - SC.card) ≥ (N - 3) * N := by
        have h2 : SR.card * N + SC.card * N ≤ 3 * N := by
          rw [← Nat.add_mul]; exact Nat.mul_le_mul_right N hab_le
        have h3 : (N - SR.card) * (N - SC.card) + SR.card * N + SC.card * N =
            N * N + SR.card * SC.card := by
          zify [le_of_lt hSR_lt, le_of_lt hSC_lt]; ring
        have h4 : (N - 3) * N + 3 * N = N * N := by
          rw [← Nat.add_mul, Nat.sub_add_cancel (by omega)]
        omega
      have h5 : 3 * N ≤ (N - 3) * N := Nat.mul_le_mul_right N (by omega)
      omega
  set U : Finset (Fin N × Fin N) := Finset.univ.filter (fun z => z.1 ∈ SR ∨ z.2 ∈ SC)
  have hT_sub_U : T ⊆ U := by
    intro z hz
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hz
    simp only [U, Finset.mem_filter, Finset.mem_univ, true_and]
    by_contra hnot
    push_neg at hnot
    have := hout_false z.1 z.2 hnot.1 hnot.2
    rw [this] at hz; exact Bool.false_ne_true hz
  have hU_card : U.card = (SR.card + SC.card) * N - SR.card * SC.card := by
    have hU_eq : U = (SR ×ˢ Finset.univ) ∪ (Finset.univ ×ˢ SC) := by
      ext z; simp [U]
    have hU_inter : (SR ×ˢ Finset.univ) ∩ (Finset.univ ×ˢ SC) = SR ×ˢ SC := by
      ext z; simp
    have hinc := Finset.card_union_add_card_inter (SR ×ˢ (Finset.univ : Finset (Fin N)))
      ((Finset.univ : Finset (Fin N)) ×ˢ SC)
    rw [← hU_eq, hU_inter, Finset.card_product, Finset.card_product, Finset.card_product,
      Finset.card_univ, Fintype.card_fin] at hinc
    have hmul : SR.card * SC.card ≤ SR.card * N + N * SC.card := by
      calc SR.card * SC.card ≤ SR.card * N := Nat.mul_le_mul_left _ (le_of_lt hSC_lt)
        _ ≤ SR.card * N + N * SC.card := Nat.le_add_right _ _
    have hadd : (SR.card + SC.card) * N = SR.card * N + N * SC.card := by ring
    omega
  have hTU := Finset.card_le_card hT_sub_U
  have hsum3 : SR.card + SC.card = 3 := by
    by_contra h
    have hle2 : SR.card + SC.card ≤ 2 := by omega
    have : (SR.card + SC.card) * N ≤ 2 * N := Nat.mul_le_mul_right N hle2
    omega
  have hfin : ∀ (hc : (SR.card = 2 ∧ SC.card = 1) ∨ (SR.card = 1 ∧ SC.card = 2)),
      ∃ SR SC : Finset (Fin N), ((SR.card = 2 ∧ SC.card = 1) ∨ (SR.card = 1 ∧ SC.card = 2)) ∧
      ∀ x y : Fin N, C.eval (oneEach x y) = true ↔ (x ∈ SR ∨ y ∈ SC) := by
    intro hc
    refine ⟨SR, SC, hc, ?_⟩
    have hprod : SR.card * SC.card = 2 := by
      rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
    have hTeq : T = U := Finset.eq_of_subset_of_card_le hT_sub_U (by
      rw [hU_card, hsum3, hprod]; omega)
    intro x y
    have : (x, y) ∈ T ↔ (x, y) ∈ U := by rw [hTeq]
    simpa [T, U, tbl] using this
  have hcases : (SR.card = 2 ∧ SC.card = 1) ∨ (SR.card = 1 ∧ SC.card = 2) ∨ SC.card = 0 ∨
      SR.card = 0 := by omega
  rcases hcases with h | h | h | h
  · exact hfin (Or.inl h)
  · exact hfin (Or.inr h)
  · exfalso
    have hSCe : SC = ∅ := Finset.card_eq_zero.mp h
    set R' : Finset (Fin N) := Finset.univ.filter (fun x => tbl x y0 = true)
    have hTR : T = R' ×ˢ Finset.univ := by
      ext z
      simp only [T, R', Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product, and_true]
      rw [h_agree z.1 z.2 z.1 y0 (fun _ _ => Iff.rfl) (by intro b hb; rw [hSCe] at hb; simp at hb)]
    rw [hTR, Finset.card_product, Finset.card_univ, Fintype.card_fin] at harea
    rcases Nat.lt_or_ge R'.card 3 with h3 | h3
    · have : R'.card * N ≤ 2 * N := Nat.mul_le_mul_right N (by omega)
      omega
    · have : 3 * N ≤ R'.card * N := Nat.mul_le_mul_right N h3
      omega
  · exfalso
    have hSRe : SR = ∅ := Finset.card_eq_zero.mp h
    set C' : Finset (Fin N) := Finset.univ.filter (fun y => tbl x0 y = true)
    have hTC : T = Finset.univ ×ˢ C' := by
      ext z
      simp only [T, C', Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product]
      rw [h_agree z.1 z.2 x0 z.2 (by intro a ha; rw [hSRe] at ha; simp at ha) (fun _ _ => Iff.rfl)]
    rw [hTC, Finset.card_product, Finset.card_univ, Fintype.card_fin] at harea
    rcases Nat.lt_or_ge C'.card 3 with h3 | h3
    · have : N * C'.card ≤ N * 2 := Nat.mul_le_mul_left N (by omega)
      omega
    · have : N * 3 ≤ N * C'.card := Nat.mul_le_mul_left N h3
      omega

lemma sum_mem_ite {α : Type*} [Fintype α] [DecidableEq α] (s : Finset α) (g : α → ℕ) :
    ∑ x ∈ s, g x = ∑ x, if x ∈ s then g x else 0 := by
  rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]

lemma rowcol {N : ℕ} (SR SC : Finset (Fin N)) (Q : Fin N → Fin N → Prop)
    [∀ x y, Decidable (Q x y)] :
    ((Finset.univ : Finset (Fin N × Fin N)).filter (fun z => (z.1 ∈ SR ∨ z.2 ∈ SC) ∧ Q z.1 z.2)).card +
    ∑ x ∈ SR, ∑ y ∈ SC, (if Q x y then 1 else 0) =
    ∑ x ∈ SR, ((Finset.univ : Finset (Fin N)).filter (fun y => Q x y)).card +
    ∑ y ∈ SC, ((Finset.univ : Finset (Fin N)).filter (fun x => Q x y)).card := by
  rw [Finset.card_filter, Fintype.sum_prod_type]
  simp only [Finset.card_filter]
  rw [sum_mem_ite SR, sum_mem_ite SR, sum_mem_ite SC]
  have e1 : ∀ x : Fin N, (if x ∈ SR then ∑ y ∈ SC, (if Q x y then 1 else 0) else 0) =
      ∑ y, (if x ∈ SR ∧ y ∈ SC ∧ Q x y then 1 else 0) := by
    intro x
    rw [sum_mem_ite SC]
    split_ifs with hx
    · apply Finset.sum_congr rfl; intro y _; by_cases hy : y ∈ SC <;> by_cases hq : Q x y <;> simp [hx, hy, hq]
    · simp [hx]
  have e2 : ∀ x : Fin N, (if x ∈ SR then ∑ y, (if Q x y then 1 else 0) else 0) =
      ∑ y, (if x ∈ SR ∧ Q x y then 1 else 0) := by
    intro x
    split_ifs with hx
    · apply Finset.sum_congr rfl; intro y _; by_cases hq : Q x y <;> simp [hx, hq]
    · simp [hx]
  have e3 : ∀ y : Fin N, (if y ∈ SC then ∑ x, (if Q x y then 1 else 0) else 0) =
      ∑ x, (if y ∈ SC ∧ Q x y then 1 else 0) := by
    intro y
    split_ifs with hy
    · apply Finset.sum_congr rfl; intro x _; by_cases hq : Q x y <;> simp [hy, hq]
    · simp [hy]
  simp only [e1, e2, e3]
  rw [Finset.sum_comm (f := fun y x => if y ∈ SC ∧ Q x y then 1 else 0)]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hx : x ∈ SR <;> by_cases hy : y ∈ SC <;> by_cases hq : Q x y <;> simp [hx, hy, hq]

lemma ov_formula {N t : ℕ} (ht : t ≤ N) (P : Fin N × Fin N → Bool) (SR SC : Finset (Fin N))
    (hP : ∀ x y, P (x, y) = true ↔ x ∈ SR ∨ y ∈ SC) (u : ℕ) :
    ((Finset.univ : Finset (Fin N × Fin N)).filter
      (fun z => P z = true ∧ targetI N t u z.1 z.2 = true)).card +
      ∑ x ∈ SR, ∑ y ∈ SC, (if targetI N t u x y = true then 1 else 0) = (SR.card + SC.card) * t := by
  have h := rowcol SR SC (fun x y => targetI N t u x y = true)
  have hf : (Finset.univ : Finset (Fin N × Fin N)).filter
      (fun z => P z = true ∧ targetI N t u z.1 z.2 = true) =
      (Finset.univ : Finset (Fin N × Fin N)).filter
      (fun z => (z.1 ∈ SR ∨ z.2 ∈ SC) ∧ targetI N t u z.1 z.2 = true) := by
    apply Finset.filter_congr
    intro z _
    rw [← hP z.1 z.2]
  rw [hf, h]
  simp only [card_targetI_col ht, card_targetI_row ht, Finset.sum_const, smul_eq_mul]
  ring

lemma area_formula {N : ℕ} (P : Fin N × Fin N → Bool) (SR SC : Finset (Fin N))
    (hP : ∀ x y, P (x, y) = true ↔ x ∈ SR ∨ y ∈ SC) :
    ((Finset.univ : Finset (Fin N × Fin N)).filter (fun z => P z = true)).card +
      SR.card * SC.card = (SR.card + SC.card) * N := by
  have h := rowcol SR SC (fun _ _ => True)
  have hf : (Finset.univ : Finset (Fin N × Fin N)).filter (fun z => P z = true) =
      (Finset.univ : Finset (Fin N × Fin N)).filter (fun z => (z.1 ∈ SR ∨ z.2 ∈ SC) ∧ True) := by
    apply Finset.filter_congr
    intro z _
    rw [← hP z.1 z.2, and_true]
  rw [hf]
  have h2 : ∑ x ∈ SR, ∑ y ∈ SC, (if True then 1 else 0) = SR.card * SC.card := by simp
  have h3 : ∑ x ∈ SR, ((Finset.univ : Finset (Fin N)).filter (fun _ => True)).card = SR.card * N := by
    simp
  have h4 : ∑ y ∈ SC, ((Finset.univ : Finset (Fin N)).filter (fun _ => True)).card = SC.card * N := by
    simp
  rw [h2, h3, h4] at h
  rw [h]
  ring


section Abstract

open Fin.CommRing

variable {N : ℕ} [NeZero N]


def winR (t : ℕ) (u d : Fin N) : ℝ := if (d - u).val < t then 1 else 0

def Sw (t : ℕ) (m : Fin N → ℝ) (u : Fin N) : ℝ := ∑ d, m d * winR t u d

lemma Sw_eq_range {t : ℕ} (ht : t ≤ N) (m : Fin N → ℝ) (u : Fin N) :
    Sw t m u = ∑ k ∈ range t, m (u + (k : Fin N)) := by
  unfold Sw winR
  rw [← Fintype.sum_equiv (Equiv.addLeft u)
    (fun j => m (u + j) * (if j.val < t then 1 else 0)) _ (by intro j; simp)]
  have h1 : ∑ j : Fin N, m (u + j) * (if j.val < t then (1:ℝ) else 0) =
      ∑ k ∈ range N, m (u + (k : Fin N)) * (if k < t then (1:ℝ) else 0) := by
    rw [← Fin.sum_univ_eq_sum_range (fun k => m (u + (k : Fin N)) * (if k < t then (1:ℝ) else 0)) N]
    apply sum_congr rfl
    intro j _
    simp
  rw [h1, ← Finset.sum_range_add_sum_Ico _ ht]
  have h2 : ∑ k ∈ Ico t N, m (u + (k : Fin N)) * (if k < t then (1:ℝ) else 0) = 0 := by
    apply sum_eq_zero
    intro k hk
    rw [mem_Ico] at hk
    simp [show ¬ k < t by omega]
  rw [h2, add_zero]
  apply sum_congr rfl
  intro k hk
  rw [mem_range] at hk
  simp [hk]

lemma Sw_succ {t : ℕ} (ht : t ≤ N) (m : Fin N → ℝ) (u : Fin N) :
    Sw t m (u + 1) + m u = Sw t m u + m (u + (t : Fin N)) := by
  rw [Sw_eq_range ht, Sw_eq_range ht]
  have h1 : ∑ k ∈ range (t+1), m (u + (k : Fin N)) =
      ∑ k ∈ range t, m (u + 1 + (k : Fin N)) + m u := by
    rw [Finset.sum_range_succ']
    congr 1
    · apply sum_congr rfl
      intro k _
      congr 1
      push_cast
      ring
    · simp
  have h2 : ∑ k ∈ range (t+1), m (u + (k : Fin N)) =
      ∑ k ∈ range t, m (u + (k : Fin N)) + m (u + (t : Fin N)) := Finset.sum_range_succ _ _
  linarith

lemma window_iff {t : ℕ} (ht : t ≤ N) (m : Fin N → ℝ) :
    (∀ u, Sw t m u = Sw t m 0) ↔ ∀ d, m (d + (t : Fin N)) = m d := by
  constructor
  · intro h d
    have := Sw_succ ht m d
    rw [h (d+1), h d] at this
    linarith
  · intro h u
    have step : ∀ v : Fin N, Sw t m (v + 1) = Sw t m v := by
      intro v
      have := Sw_succ ht m v
      rw [h v] at this
      linarith
    have hk : ∀ k : ℕ, Sw t m (k : Fin N) = Sw t m 0 := by
      intro k
      induction k with
      | zero => simp
      | succ k ih => rw [Nat.cast_succ, step, ih]
    rw [← Fin.cast_val_eq_self u]
    exact hk u.val

def mass {ι : Type*} [Fintype ι] (c1 c2 : ι → Fin N) (w : ι → ℝ) (d : Fin N) : ℝ :=
  ∑ i, w i * ((if c1 i = d then 1 else 0) + (if c2 i = d then 1 else 0))

lemma mass_Sw {ι : Type*} [Fintype ι] (t : ℕ) (c1 c2 : ι → Fin N) (w : ι → ℝ) (u : Fin N) :
    ∑ i, w i * (winR t u (c1 i) + winR t u (c2 i)) = Sw t (mass c1 c2 w) u := by
  simp only [Sw, mass, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro i _
  simp only [mul_assoc, ← Finset.mul_sum]
  congr 1
  simp [add_mul, Finset.sum_add_distrib, ite_mul]

lemma avg_iff (F : Fin N → ℝ) (B : ℝ) (hsum : ∑ u, F u = B) :
    (∀ u, (N : ℝ) * F u ≤ B) ↔ ∀ u, F u = F 0 := by
  have hNpos : (0 : ℝ) < N := by
    have : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
    exact_mod_cast this
  constructor
  · intro h
    have hz : ∑ u, (B - (N : ℝ) * F u) = 0 := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hsum]
      simp
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun u _ => by linarith [h u])] at hz
    intro u
    have h1 := hz u (mem_univ _)
    have h2 := hz 0 (mem_univ _)
    have : (N : ℝ) * F u = N * F 0 := by linarith
    exact mul_left_cancel₀ (ne_of_gt hNpos) this
  · intro h u
    have : ∑ u, F u = N * F 0 := by
      rw [Finset.sum_congr rfl (fun v _ => h v)]
      simp
    rw [h u]
    linarith

/-! orbits of `t` -/

lemma L_pos {t : ℕ} : 0 < N / Nat.gcd N t := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  exact Nat.div_pos (Nat.gcd_le_left t hN) (Nat.gcd_pos_of_pos_left t hN)

lemma LT_zero (t : ℕ) : ((N / Nat.gcd N t : ℕ) : Fin N) * (t : Fin N) = 0 := by
  rw [← Nat.cast_mul, Fin.natCast_eq_zero]
  have hg := Nat.gcd_dvd_left N t
  obtain ⟨t', ht'⟩ := Nat.gcd_dvd_right N t
  refine ⟨t', ?_⟩
  calc N / Nat.gcd N t * t = N / Nat.gcd N t * (Nat.gcd N t * t') := by rw [← ht']
    _ = N / Nat.gcd N t * Nat.gcd N t * t' := by ring
    _ = N * t' := by rw [Nat.div_mul_cancel hg]

lemma orb_inj {t k1 k2 : ℕ} (h1 : k1 < N / Nat.gcd N t) (h2 : k2 < N / Nat.gcd N t)
    (h : (k1 : Fin N) * (t : Fin N) = (k2 : Fin N) * (t : Fin N)) : k1 = k2 := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  rw [← Nat.cast_mul, ← Nat.cast_mul, Fin.ext_iff, Fin.val_natCast, Fin.val_natCast] at h
  have hm : t * k1 ≡ t * k2 [MOD N] := by
    unfold Nat.ModEq
    rw [Nat.mul_comm t k1, Nat.mul_comm t k2]
    exact h
  exact Nat.ModEq.eq_of_lt_of_lt (Nat.ModEq.cancel_left_div_gcd hN hm) h1 h2

lemma orb_mod (t k : ℕ) :
    (k : Fin N) * (t : Fin N) = ((k % (N / Nat.gcd N t) : ℕ) : Fin N) * (t : Fin N) := by
  have hz := LT_zero (N := N) t
  set L := N / Nat.gcd N t
  conv_lhs => rw [← Nat.mod_add_div k L]
  push_cast
  linear_combination ((k / L : ℕ) : Fin N) * hz

def orbF (t : ℕ) (d : Fin N) : Finset (Fin N) :=
  (range (N / Nat.gcd N t)).image (fun k : ℕ => d + (k : Fin N) * (t : Fin N))

lemma card_orbF (t : ℕ) (d : Fin N) : (orbF t d).card = N / Nat.gcd N t := by
  unfold orbF
  rw [card_image_of_injOn, card_range]
  intro a ha b hb hab
  simp only [coe_range, Set.mem_Iio] at ha hb
  exact orb_inj ha hb (add_left_cancel hab)

lemma mem_orbF {t : ℕ} {d e : Fin N} : e ∈ orbF t d ↔ ∃ k : ℕ, e = d + (k : Fin N) * (t : Fin N) := by
  unfold orbF
  rw [mem_image]
  constructor
  · rintro ⟨k, _, rfl⟩
    exact ⟨k, rfl⟩
  · rintro ⟨k, rfl⟩
    refine ⟨k % (N / Nat.gcd N t), mem_range.mpr (Nat.mod_lt _ L_pos), ?_⟩
    rw [← orb_mod]

lemma neg_T_eq (t : ℕ) : ∃ k : ℕ, (k : Fin N) * (t : Fin N) = - (t : Fin N) := by
  have hz := LT_zero (N := N) t
  have hL := L_pos (N := N) (t := t)
  refine ⟨N / Nat.gcd N t - 1, ?_⟩
  have hc : ((N / Nat.gcd N t - 1 : ℕ) : Fin N) = ((N / Nat.gcd N t : ℕ) : Fin N) - 1 := by
    rw [Nat.cast_sub (by omega)]
    simp
  rw [hc]
  linear_combination hz

lemma orbF_add {t : ℕ} {d e : Fin N} (h : e ∈ orbF t d) : e + (t : Fin N) ∈ orbF t d := by
  rw [mem_orbF] at h ⊢
  obtain ⟨k, rfl⟩ := h
  exact ⟨k + 1, by push_cast; ring⟩

lemma orbF_sub {t : ℕ} {d e : Fin N} (h : e + (t : Fin N) ∈ orbF t d) : e ∈ orbF t d := by
  rw [mem_orbF] at h ⊢
  obtain ⟨k, hk⟩ := h
  obtain ⟨j, hj⟩ := neg_T_eq (N := N) t
  exact ⟨k + j, by push_cast; linear_combination hk - hj⟩

lemma orbF_self (t : ℕ) (d : Fin N) : d ∈ orbF t d := mem_orbF.mpr ⟨0, by simp⟩

lemma orbF_disj {t : ℕ} {d0 d1 : Fin N} (h : d1 ∉ orbF t d0) : Disjoint (orbF t d1) (orbF t d0) := by
  rw [Finset.disjoint_left]
  intro e he1 he0
  apply h
  rw [mem_orbF] at he1 he0 ⊢
  obtain ⟨a, ha⟩ := he1
  obtain ⟨b, hb⟩ := he0
  obtain ⟨j, hj⟩ := neg_T_eq (N := N) t
  refine ⟨b + a * j, ?_⟩
  push_cast
  linear_combination hb - ha - (a : Fin N) * hj

lemma per_orb {t : ℕ} (m : Fin N → ℝ) (hper : ∀ d, m (d + (t : Fin N)) = m d) (d : Fin N) :
    ∀ e ∈ orbF t d, m e = m d := by
  have hk : ∀ k : ℕ, m (d + (k : Fin N) * (t : Fin N)) = m d := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have : d + ((k + 1 : ℕ) : Fin N) * (t : Fin N) = (d + (k : Fin N) * (t : Fin N)) + (t : Fin N) := by
        push_cast; ring
      rw [this, hper, ih]
  intro e he
  obtain ⟨k, rfl⟩ := mem_orbF.mp he
  exact hk k


lemma T_ne_zero {t : ℕ} (htN : N < 2 * t) (hL : N / Nat.gcd N t ≠ 1) : (t : Fin N) ≠ 0 := by
  intro h
  rw [Fin.natCast_eq_zero] at h
  apply hL
  have hg : Nat.gcd N t = N := Nat.gcd_eq_left h
  rw [hg, Nat.div_self (Nat.pos_of_ne_zero (NeZero.ne N))]

lemma T2_ne_zero {t : ℕ} (ht : t ≤ N) (htN : N < 2 * t) (hL : N / Nat.gcd N t ≠ 1) :
    (2 : Fin N) * (t : Fin N) ≠ 0 := by
  intro h
  have h' : ((2 * t : ℕ) : Fin N) = 0 := by push_cast; exact h
  rw [Fin.natCast_eq_zero] at h'
  obtain ⟨c, hc⟩ := h'
  have hc1 : c = 1 ∨ c = 2 := by
    rcases Nat.lt_or_ge c 3 with h3 | h3
    · interval_cases c <;> simp_all <;> omega
    · exfalso
      have : N * 3 ≤ N * c := Nat.mul_le_mul_left N h3
      omega
  rcases hc1 with rfl | rfl
  · omega
  · apply T_ne_zero htN hL
    rw [Fin.natCast_eq_zero]
    exact ⟨1, by omega⟩

/-- the combinatorial lower bound -/
lemma clb {t : ℕ} (ht : t ≤ N) (htN : N < 2 * t) (M : ℕ) (c1 c2 : Fin M → Fin N)
    (hc : ∀ i, c1 i ≠ c2 i) (w : Fin M → ℝ) (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (hper : ∀ d, mass c1 c2 w (d + (t : Fin N)) = mass c1 c2 w d) :
    (if N / Nat.gcd N t = 1 then 1 else if (N / Nat.gcd N t) % 2 = 0 then (N / Nat.gcd N t) / 2
      else (N / Nat.gcd N t + 3) / 2) ≤ M := by
  set L := N / Nat.gcd N t with hLdef
  have hLpos : 0 < L := L_pos
  set m := mass c1 c2 w with hmdef
  set P := (univ : Finset (Fin M)).filter (fun i => 0 < w i) with hPdef
  have hPM : P.card ≤ M := (card_filter_le _ _).trans (by simp)
  have hcard : ∀ d : Fin N, (orbF t d).card = L := fun d => by rw [card_orbF]
  set deg : Fin N → ℕ := fun d => (P.filter (fun i => c1 i = d ∨ c2 i = d)).card with hdegdef
  have hm : ∀ d, m d = ∑ i ∈ P.filter (fun i => c1 i = d ∨ c2 i = d), w i := by
    intro d
    simp only [hmdef, mass, hPdef]
    rw [Finset.filter_filter, Finset.sum_filter]
    apply sum_congr rfl
    intro i _
    by_cases hw : 0 < w i
    · by_cases h1 : c1 i = d <;> by_cases h2 : c2 i = d
      · exact absurd (h1.trans h2.symm) (hc i)
      all_goals simp [hw, h1, h2]
    · have : w i = 0 := le_antisymm (not_lt.mp hw) (hw0 i)
      simp [this]
  have hdeg_sum : ∑ d, deg d = 2 * P.card := by
    simp only [hdegdef, card_filter]
    rw [Finset.sum_comm, Finset.card_eq_sum_ones, Finset.mul_sum]
    apply sum_congr rfl
    intro i _
    rw [← card_filter]
    have : (univ : Finset (Fin N)).filter (fun d => c1 i = d ∨ c2 i = d) = {c1 i, c2 i} := by
      ext d; simp [eq_comm]
    rw [this, card_pair (hc i)]
    simp
  have hpos_iff : ∀ d, 0 < m d ↔ 0 < deg d := by
    intro d
    rw [hm d]
    constructor
    · intro h
      by_contra h0
      have h00 : deg d = 0 := by omega
      simp only [hdegdef] at h00
      rw [card_eq_zero] at h00
      rw [h00] at h
      simp at h
    · intro h
      apply Finset.sum_pos
      · intro i hi
        exact (mem_filter.mp (mem_filter.mp hi).1).2
      · exact card_pos.mp h
  obtain ⟨i0, hi0⟩ : P.Nonempty := by
    by_contra hne
    rw [not_nonempty_iff_eq_empty] at hne
    have hz : ∀ i, w i = 0 := by
      intro i
      have : i ∉ P := by rw [hne]; simp
      simp only [hPdef, mem_filter, mem_univ, true_and, not_lt] at this
      exact le_antisymm this (hw0 i)
    simp [hz] at hw1
  set d0 := c1 i0 with hd0
  have hd0deg : 0 < deg d0 := by
    apply card_pos.mpr
    exact ⟨i0, mem_filter.mpr ⟨hi0, Or.inl rfl⟩⟩
  have hO := per_orb m hper d0
  have hdegO : ∀ e ∈ orbF t d0, 1 ≤ deg e := by
    intro e he
    have := (hpos_iff e).mp (by rw [hO e he]; exact (hpos_iff d0).mpr hd0deg)
    omega
  have hsumO : L ≤ ∑ e ∈ orbF t d0, deg e := by
    have := Finset.card_nsmul_le_sum (orbF t d0) deg 1 hdegO
    rw [hcard] at this
    simpa using this
  have hsplit : ∑ e ∈ univ \ orbF t d0, deg e + ∑ e ∈ orbF t d0, deg e = 2 * P.card := by
    rw [Finset.sum_sdiff (subset_univ _), hdeg_sum]
  have hL2P : L ≤ 2 * P.card := by omega
  have hP1 : 1 ≤ P.card := card_pos.mpr ⟨i0, hi0⟩
  by_cases hL1 : L = 1
  · simp only [hL1, ↓reduceIte]; omega
  simp only [hL1, ↓reduceIte]
  by_cases hLe : L % 2 = 0
  · simp only [hLe, ↓reduceIte]; omega
  simp only [hLe, ↓reduceIte]
  by_contra hlt
  have h2P : 2 * P.card ≤ L + 1 := by omega
  have hL3 : 3 ≤ L := by omega
  -- vertices of positive degree lie on the orbit of d0
  have hoff : ∀ e, e ∉ orbF t d0 → deg e = 0 := by
    intro e he
    by_contra hne
    have hpe : 0 < m e := (hpos_iff e).mpr (by omega)
    have hOe := per_orb m hper e
    have hdegOe : ∀ x ∈ orbF t e, 1 ≤ deg x := by
      intro x hx
      have := (hpos_iff x).mp (by rw [hOe x hx]; exact hpe)
      omega
    have hsub : orbF t e ⊆ univ \ orbF t d0 := by
      intro x hx
      rw [mem_sdiff]
      exact ⟨mem_univ _, Finset.disjoint_left.mp (orbF_disj he) hx⟩
    have h1 : L ≤ ∑ x ∈ orbF t e, deg x := by
      have := Finset.card_nsmul_le_sum (orbF t e) deg 1 hdegOe
      rw [hcard] at this
      simpa using this
    have h2 : ∑ x ∈ orbF t e, deg x ≤ ∑ x ∈ univ \ orbF t d0, deg x :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)
    omega
  have hzero : ∑ e ∈ univ \ orbF t d0, deg e = 0 := by
    apply sum_eq_zero
    intro e he
    exact hoff e (mem_sdiff.mp he).2
  obtain ⟨b, hbO, hb2⟩ : ∃ b ∈ orbF t d0, 2 ≤ deg b := by
    by_contra hall
    push_neg at hall
    have : ∑ e ∈ orbF t d0, deg e = ∑ e ∈ orbF t d0, 1 := by
      apply sum_congr rfl
      intro e he
      have := hdegO e he
      have := hall e he
      omega
    have hs1 : ∑ e ∈ orbF t d0, deg e = L := by rw [this, sum_const, hcard]; simp
    omega
  have hle1 : ∀ a ∈ orbF t d0, a ≠ b → deg a ≤ 1 := by
    intro a ha hab
    have hsub : ({a, b} : Finset (Fin N)) ⊆ orbF t d0 := by
      intro x hx
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    have h1 : ∑ e ∈ orbF t d0, deg e = ∑ e ∈ orbF t d0, 1 + ∑ e ∈ orbF t d0, (deg e - 1) := by
      rw [← Finset.sum_add_distrib]
      apply sum_congr rfl
      intro e he
      have := hdegO e he
      omega
    have h2 : ∑ e ∈ ({a, b} : Finset (Fin N)), (deg e - 1) ≤ ∑ e ∈ orbF t d0, (deg e - 1) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)
    rw [sum_pair hab] at h2
    rw [sum_const, hcard] at h1
    simp at h1
    omega
  obtain ⟨i, hi⟩ : (P.filter (fun i => c1 i = b ∨ c2 i = b)).Nonempty := card_pos.mp (Nat.lt_of_lt_of_le (by norm_num : 0 < 2) hb2)
  have hiP := (mem_filter.mp hi).1
  have hib := (mem_filter.mp hi).2
  set a := if c1 i = b then c2 i else c1 i with hadef
  have hab : a ≠ b := by
    simp only [hadef]
    split_ifs with h
    · intro h'; exact hc i (h.trans h'.symm)
    · exact h
  have hia : c1 i = a ∨ c2 i = a := by
    simp only [hadef]
    split_ifs with h
    · exact Or.inr rfl
    · exact Or.inl rfl
  have hadeg : 0 < deg a := card_pos.mpr ⟨i, mem_filter.mpr ⟨hiP, hia⟩⟩
  have haO : a ∈ orbF t d0 := by
    by_contra h
    have := hoff a h
    omega
  have hsing : P.filter (fun j => c1 j = a ∨ c2 j = a) = {i} := by
    have h1 := hle1 a haO hab
    have hmem : i ∈ P.filter (fun j => c1 j = a ∨ c2 j = a) := mem_filter.mpr ⟨hiP, hia⟩
    exact Finset.eq_singleton_iff_unique_mem.mpr ⟨hmem, fun y hy => Finset.card_le_one.mp h1 y hy i hmem⟩
  have hma : m a = w i := by rw [hm a, hsing, sum_singleton]
  obtain ⟨j, hj, hji⟩ := Finset.exists_mem_ne (show 1 < (P.filter (fun i => c1 i = b ∨ c2 i = b)).card by
    simp only [hdegdef] at hb2; omega) i
  have hmb : w i + w j ≤ m b := by
    rw [hm b, ← sum_pair (Ne.symm hji)]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro x hx
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    · intro x _ _; exact hw0 x
  have hwj : 0 < w j := (mem_filter.mp (mem_filter.mp hj).1).2
  have heq : m a = m b := by rw [hO a haO, hO b hbO]
  linarith

/-- vertex counts along the orbit of `0` are periodic -/
lemma cnt_per (t : ℕ) (d : Fin N) :
    ∑ k ∈ range (N / Nat.gcd N t), (if (k : Fin N) * (t : Fin N) = d + (t : Fin N) then (1:ℝ) else 0) =
    ∑ k ∈ range (N / Nat.gcd N t), (if (k : Fin N) * (t : Fin N) = d then (1:ℝ) else 0) := by
  have hz := LT_zero (N := N) t
  have hL := L_pos (N := N) (t := t)
  obtain ⟨L', hL'⟩ : ∃ L', N / Nat.gcd N t = L' + 1 := ⟨N / Nat.gcd N t - 1, by omega⟩
  rw [hL'] at hz ⊢
  rw [Finset.sum_range_succ', Finset.sum_range_succ]
  congr 1
  · apply sum_congr rfl
    intro k _
    have : ((k + 1 : ℕ) : Fin N) * (t : Fin N) = d + (t : Fin N) ↔ (k : Fin N) * (t : Fin N) = d := by
      push_cast
      constructor
      · intro h; linear_combination h
      · intro h; linear_combination h
    simp only [this]
  · have : ((0 : ℕ) : Fin N) * (t : Fin N) = d + (t : Fin N) ↔ (L' : Fin N) * (t : Fin N) = d := by
      push_cast at hz ⊢
      constructor
      · intro h; linear_combination hz + h
      · intro h; linear_combination h - hz
    simp only [this]

lemma sum_pairs (f : ℕ → ℝ) (n : ℕ) :
    ∑ k ∈ range (2 * n), f k = ∑ i ∈ range n, (f (2 * i) + f (2 * i + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      sum_range_succ]
    ring

/-- generic construction from natural-indexed edges -/
lemma con_of {t : ℕ} (M K : ℕ) (hKM : K ≤ M) (e1 e2 : ℕ → Fin N) (om : ℕ → ℝ)
    (he : ∀ i, e1 i ≠ e2 i) (hom0 : ∀ i, 0 ≤ om i) (homK : ∀ i, K ≤ i → om i = 0)
    (hsum : ∑ i ∈ range K, om i = 1)
    (hper : ∀ d, ∑ i ∈ range K, om i * ((if e1 i = d + (t : Fin N) then 1 else 0) +
        (if e2 i = d + (t : Fin N) then 1 else 0)) =
      ∑ i ∈ range K, om i * ((if e1 i = d then 1 else 0) + (if e2 i = d then 1 else 0))) :
    ∃ (c1 c2 : Fin M → Fin N) (w : Fin M → ℝ), (∀ i, c1 i ≠ c2 i) ∧ (∀ i, 0 ≤ w i) ∧
      ∑ i, w i = 1 ∧ ∀ d, mass c1 c2 w (d + (t : Fin N)) = mass c1 c2 w d := by
  have hcut : ∀ g : ℕ → ℝ, ∑ i : Fin M, om i.val * g i.val = ∑ i ∈ range K, om i * g i := by
    intro g
    rw [Fin.sum_univ_eq_sum_range (fun i => om i * g i) M, ← Finset.sum_range_add_sum_Ico _ hKM]
    have : ∑ i ∈ Ico K M, om i * g i = 0 := by
      apply sum_eq_zero
      intro i hi
      rw [homK i (mem_Ico.mp hi).1, zero_mul]
    rw [this, add_zero]
  refine ⟨fun i => e1 i.val, fun i => e2 i.val, fun i => om i.val, fun i => he i.val,
    fun i => hom0 i.val, ?_, ?_⟩
  · have := hcut (fun _ => 1)
    simp only [mul_one] at this
    rw [this, hsum]
  · intro d
    simp only [mass]
    rw [hcut (fun i => (if e1 i = d + (t : Fin N) then 1 else 0) + (if e2 i = d + (t : Fin N) then 1 else 0)),
      hcut (fun i => (if e1 i = d then 1 else 0) + (if e2 i = d then 1 else 0))]
    exact hper d

lemma con {t : ℕ} (hN : 1 < N) (ht : t ≤ N) (htN : N < 2 * t) (M : ℕ)
    (hM : (if N / Nat.gcd N t = 1 then 1 else if (N / Nat.gcd N t) % 2 = 0 then (N / Nat.gcd N t) / 2
      else (N / Nat.gcd N t + 3) / 2) ≤ M) :
    ∃ (c1 c2 : Fin M → Fin N) (w : Fin M → ℝ), (∀ i, c1 i ≠ c2 i) ∧ (∀ i, 0 ≤ w i) ∧
      ∑ i, w i = 1 ∧ ∀ d, mass c1 c2 w (d + (t : Fin N)) = mass c1 c2 w d := by
  set L := N / Nat.gcd N t with hLdef
  have hLpos : 0 < L := L_pos
  set T : Fin N := (t : Fin N) with hTdef
  by_cases hL1 : L = 1
  · simp only [hL1, ↓reduceIte] at hM
    have hT0 : T = 0 := by
      have h1 : Nat.gcd N t = N := by
        have hg := Nat.gcd_le_left t (show 0 < N by omega)
        have hd := Nat.div_mul_cancel (Nat.gcd_dvd_left N t)
        rw [← hLdef, hL1, one_mul] at hd
        exact hd
      rw [hTdef, Fin.natCast_eq_zero, ← h1]
      exact Nat.gcd_dvd_right N t
    have h01 : (0 : Fin N) ≠ 1 := by
      intro h
      have := congrArg Fin.val h
      simp [Fin.val_one', Nat.mod_eq_of_lt hN] at this
    refine con_of M 1 hM (fun _ => 0) (fun _ => 1) (fun i => if i = 0 then 1 else 0)
      (fun _ => h01) (fun i => by split_ifs <;> norm_num) (fun i hi => by simp; omega) (by simp) ?_
    intro d
    rw [← hTdef, hT0, add_zero]
  have hT : T ≠ 0 := T_ne_zero htN hL1
  have hT2 : (2 : Fin N) * T ≠ 0 := T2_ne_zero ht htN hL1
  simp only [hL1, ↓reduceIte] at hM
  have hLr : (L : ℝ) ≠ 0 := by exact_mod_cast hLpos.ne'
  -- the orbit count
  set f : Fin N → ℕ → ℝ := fun d k => if (k : Fin N) * T = d then 1 else 0 with hfdef
  have hfper : ∀ d, ∑ k ∈ range L, f (d + T) k = ∑ k ∈ range L, f d k := fun d => cnt_per t d
  have hdist : ∀ a δ : ℕ, (δ = 1 ∨ δ = 2) → (a : Fin N) * T ≠ ((a + δ : ℕ) : Fin N) * T := by
    intro a δ hδ h
    push_cast at h
    rcases hδ with rfl | rfl
    · apply hT; linear_combination -h
    · apply hT2; push_cast at h; linear_combination -h
  by_cases hLe : L % 2 = 0
  · simp only [hLe, ↓reduceIte] at hM
    refine con_of M (L / 2) hM (fun i => ((2 * i : ℕ) : Fin N) * T)
      (fun i => ((2 * i + 1 : ℕ) : Fin N) * T) (fun i => if i < L / 2 then 2 / L else 0)
      (fun i => hdist (2 * i) 1 (Or.inl rfl)) (fun i => by
        split_ifs
        · positivity
        · exact le_refl _)
      (fun i hi => by simp; omega) ?_ ?_
    · rw [Finset.sum_congr rfl (fun i hi => if_pos (mem_range.mp hi)), sum_const, card_range,
        nsmul_eq_mul]
      have : ((L / 2 : ℕ) : ℝ) * 2 = L := by
        have : L / 2 * 2 = L := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hLe)
        exact_mod_cast this
      field_simp
      linarith
    · intro d
      have key : ∀ d', ∑ i ∈ range (L / 2), (if i < L / 2 then 2 / (L : ℝ) else 0) *
          ((if ((2 * i : ℕ) : Fin N) * T = d' then 1 else 0) +
            (if ((2 * i + 1 : ℕ) : Fin N) * T = d' then 1 else 0)) =
          2 / L * ∑ k ∈ range L, f d' k := by
        intro d'
        have hL2 : L = 2 * (L / 2) := by omega
        have hsp : ∑ k ∈ range L, f d' k = ∑ i ∈ range (L / 2), (f d' (2 * i) + f d' (2 * i + 1)) := by
          conv_lhs => rw [hL2]
          exact sum_pairs _ _
        rw [hsp, Finset.mul_sum]
        apply sum_congr rfl
        intro i hi
        rw [if_pos (mem_range.mp hi)]
      rw [key, key, hfper]
  · simp only [hLe, ↓reduceIte] at hM
    obtain ⟨J, hJ⟩ : ∃ J, L = 2 * J + 3 := ⟨(L - 3) / 2, by omega⟩
    have hK : (L + 3) / 2 = 3 + J := by omega
    rw [hK] at hM
    set a : ℕ → ℕ := fun i => if i = 0 then 0 else if i = 1 then 1 else if i = 2 then 0 else 2 * i - 3
      with hadef
    set δ : ℕ → ℕ := fun i => if i = 2 then 2 else 1 with hδdef
    refine con_of M (3 + J) hM (fun i => ((a i : ℕ) : Fin N) * T)
      (fun i => ((a i + δ i : ℕ) : Fin N) * T)
      (fun i => if i < 3 then 1 / L else if i < 3 + J then 2 / L else 0)
      (fun i => hdist (a i) (δ i) (by simp only [hδdef]; split_ifs <;> simp)) (fun i => by
        split_ifs <;> first | positivity | exact le_refl _)
      (fun i hi => by rw [if_neg (by omega), if_neg (by omega)]) ?_ ?_
    · rw [Finset.sum_range_add]
      simp only [Finset.sum_range_succ, Finset.sum_range_zero]
      rw [Finset.sum_congr rfl (fun j hj => show (if 3 + j < 3 then 1 / (L : ℝ) else
          if 3 + j < 3 + J then 2 / L else 0) = 2 / L by
        rw [if_neg (by omega), if_pos (by have := mem_range.mp hj; omega)])]
      rw [sum_const, card_range, nsmul_eq_mul]
      norm_num
      have : (L : ℝ) = 2 * J + 3 := by exact_mod_cast hJ
      field_simp
      linarith
    · intro d
      have key : ∀ d', ∑ i ∈ range (3 + J), (if i < 3 then 1 / (L : ℝ) else
            if i < 3 + J then 2 / L else 0) *
          ((if ((a i : ℕ) : Fin N) * T = d' then 1 else 0) +
            (if ((a i + δ i : ℕ) : Fin N) * T = d' then 1 else 0)) =
          2 / L * ∑ k ∈ range L, f d' k := by
        intro d'
        rw [hJ, show 2 * J + 3 = 3 + 2 * J by ring, Finset.sum_range_add, Finset.sum_range_add,
          sum_pairs, mul_add]
        congr 1
        · simp only [Finset.sum_range_succ, Finset.sum_range_zero, hadef, hδdef, hfdef]
          norm_num
          split_ifs <;> ring
        · rw [Finset.mul_sum]
          apply sum_congr rfl
          intro j hj
          have hj' := mem_range.mp hj
          have ha : a (3 + j) = 3 + 2 * j := by
            simp only [hadef]; split_ifs <;> omega
          have hd : δ (3 + j) = 1 := by
            simp only [hδdef]; split_ifs <;> omega
          rw [ha, hd, if_neg (by omega), if_pos (by omega)]
          simp only [hfdef]
          rw [show 3 + 2 * j + 1 = 3 + (2 * j + 1) by ring]
      rw [key, key, hfper]

/-- translates of one edge, odd length -/
lemma wper_odd {t : ℕ} (hodd : N % 2 = 1) (c1 c2 : Fin N) (w : Fin N → ℝ) :
    (∀ d, mass (fun v => c1 + v) (fun v => c2 + v) w (d + (t : Fin N)) =
      mass (fun v => c1 + v) (fun v => c2 + v) w d) ↔ ∀ e, w (e + (t : Fin N)) = w e := by
  have hform : ∀ d, mass (fun v => c1 + v) (fun v => c2 + v) w d = w (d - c1) + w (d - c2) := by
    intro d
    simp only [mass, mul_add, Finset.sum_add_distrib]
    have h1 : ∀ c : Fin N, ∑ v, w v * (if c + v = d then (1:ℝ) else 0) = w (d - c) := by
      intro c
      have : ∀ v, (c + v = d) ↔ (v = d - c) := by
        intro v; constructor
        · intro h; rw [← h]; ring
        · intro h; rw [h]; ring
      simp only [this, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_eq']
      simp
    rw [h1, h1]
  simp only [hform]
  constructor
  · intro h e
    set T : Fin N := (t : Fin N)
    set f : Fin N → ℝ := fun e => w (e + T) - w e with hfdef
    have hrel : ∀ e, f e + f (e + (c1 - c2)) = 0 := by
      intro e
      have := h (e + c1)
      simp only [hfdef]
      have e1 : e + c1 + T - c1 = e + T := by ring
      have e2 : e + c1 + T - c2 = e + (c1 - c2) + T := by ring
      have e3 : e + c1 - c1 = e := by ring
      have e4 : e + c1 - c2 = e + (c1 - c2) := by ring
      rw [e1, e2, e3, e4] at this
      linarith
    have hk : ∀ k : ℕ, f (e + (k : Fin N) * (c1 - c2)) = (-1) ^ k * f e := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        have := hrel (e + (k : Fin N) * (c1 - c2))
        have e5 : e + (k : Fin N) * (c1 - c2) + (c1 - c2) = e + ((k + 1 : ℕ) : Fin N) * (c1 - c2) := by
          push_cast; ring
        rw [e5] at this
        rw [pow_succ]
        linarith
    have hN := hk N
    rw [Fin.natCast_self, zero_mul, add_zero] at hN
    have hneg : ((-1 : ℝ)) ^ N = -1 := Odd.neg_one_pow (Nat.odd_iff.mpr hodd)
    rw [hneg] at hN
    have : f e = 0 := by linarith
    simp only [hfdef] at this
    linarith
  · intro h d
    have e1 : d + (t : Fin N) - c1 = (d - c1) + (t : Fin N) := by ring
    have e2 : d + (t : Fin N) - c2 = (d - c2) + (t : Fin N) := by ring
    rw [e1, e2, h, h]

end Abstract

section Circ2

open Fin.CommRing

def lossF (N t : ℕ) (C : Circuit) (u : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin N × Fin N)).filter (fun z => C.eval (oneEach z.1 z.2) ≠
      decide ((z.2.val + N - z.1.val + N - u % N) % N < t))).card

def areaF (N : ℕ) (C : Circuit) : ℕ :=
  ((Finset.univ : Finset (Fin N × Fin N)).filter (fun z => C.eval (oneEach z.1 z.2) = true)).card

def ovF (N t : ℕ) (C : Circuit) (u : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin N × Fin N)).filter
      (fun z => C.eval (oneEach z.1 z.2) = true ∧ targetI N t u z.1 z.2 = true)).card

lemma loss_ov {N t : ℕ} (ht : t ≤ N) (C : Circuit) (u : ℕ) :
    lossF N t C u + 2 * ovF N t C u = areaF N C + N * t :=
  loss_add_two_overlap ht (fun z => C.eval (oneEach z.1 z.2)) u

lemma sum_lossF {N t : ℕ} (hNt : N < 2 * t) (ht : t ≤ N) (C : Circuit) :
    ∑ u : Fin N, lossF N t C u.val + (2 * t - N) * areaF N C = N * (N * t) :=
  sum_loss_eq hNt ht (fun z => C.eval (oneEach z.1 z.2))

lemma lossF_mod (N t : ℕ) (C : Circuit) (s : ℕ) : lossF N t C s = lossF N t C (s % N) := by
  simp only [lossF, Nat.mod_mod]

variable {N : ℕ} [NeZero N]

lemma zero_ne_one_fin (hN : 1 < N) : (0 : Fin N) ≠ 1 := by
  intro h
  have := congrArg Fin.val h
  simp [Fin.val_one', Nat.mod_eq_of_lt hN] at this

lemma targetI_iff (t u : ℕ) (x y : Fin N) :
    targetI N t u x y = true ↔ ((y - x) - (u : Fin N)).val < t := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  unfold targetI
  rw [decide_eq_true_iff]
  have hu : u % N < N := Nat.mod_lt _ hN
  have hx := x.isLt
  have : (y.val + N - x.val + N - u % N) % N = ((y - x) - (u : Fin N)).val := by
    rw [Fin.val_sub, Fin.val_sub, Fin.val_natCast, Nat.add_mod_mod]
    congr 1
    omega
  rw [this]

def indN (t : ℕ) (c u : Fin N) : ℕ := if (c - u).val < t then 1 else 0

lemma colours_of {t : ℕ} (ht : t ≤ N) (C : Circuit) (SR SC : Finset (Fin N))
    (hc : (SR.card = 2 ∧ SC.card = 1) ∨ (SR.card = 1 ∧ SC.card = 2))
    (hP : ∀ x y : Fin N, C.eval (oneEach x y) = true ↔ (x ∈ SR ∨ y ∈ SC)) :
    ∃ c1 c2 : Fin N, c1 ≠ c2 ∧
      ∀ u : ℕ, ovF N t C u + indN t c1 (u : Fin N) + indN t c2 (u : Fin N) = 3 * t := by
  have hov : ∀ u, ovF N t C u + ∑ x ∈ SR, ∑ y ∈ SC, (if targetI N t u x y = true then 1 else 0) =
      (SR.card + SC.card) * t :=
    fun u => ov_formula ht (fun z => C.eval (oneEach z.1 z.2)) SR SC (fun x y => hP x y) u
  have hind : ∀ (u : ℕ) (x y : Fin N),
      (if targetI N t u x y = true then 1 else 0) = indN t (y - x) (u : Fin N) := by
    intro u x y
    simp only [indN, targetI_iff]
  rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · obtain ⟨r1, r2, hr, rfl⟩ := Finset.card_eq_two.mp h1
    obtain ⟨c, rfl⟩ := Finset.card_eq_one.mp h2
    refine ⟨c - r1, c - r2, fun h => hr (sub_right_injective h), ?_⟩
    intro u
    have := hov u
    rw [Finset.sum_pair hr, Finset.sum_singleton, Finset.sum_singleton, hind, hind, h1, h2] at this
    omega
  · obtain ⟨r, rfl⟩ := Finset.card_eq_one.mp h1
    obtain ⟨c1, c2, hcc, rfl⟩ := Finset.card_eq_two.mp h2
    refine ⟨c1 - r, c2 - r, fun h => hcc (sub_left_injective h), ?_⟩
    intro u
    have := hov u
    rw [Finset.sum_singleton, Finset.sum_pair hcc, hind, hind, h1, h2] at this
    omega

lemma colours_circ {t : ℕ} (hN : 5 < N) (ht : t ≤ N) (C : Circuit) (hleg : Legal N C)
    (hsize : C.size ≤ 2) (harea : areaF N C = 3 * N - 2) :
    ∃ c1 c2 : Fin N, c1 ≠ c2 ∧
      ∀ u : ℕ, ovF N t C u + indN t c1 (u : Fin N) + indN t c2 (u : Fin N) = 3 * t := by
  obtain ⟨SR, SC, hc, hP⟩ := struct_eq hN C hleg hsize harea
  exact colours_of ht C SR SC hc hP

def edgeC (N : ℕ) (c1 c2 : Fin N) : Circuit := orChain (N + N) 0 [N + c1.val, N + c2.val]

lemma edgeC_props {t : ℕ} (hN : 5 < N) (ht : t ≤ N) (c1 c2 : Fin N) (hne : c1 ≠ c2) :
    Legal N (edgeC N c1 c2) ∧ (edgeC N c1 c2).size ≤ 2 ∧ areaF N (edgeC N c1 c2) = 3 * N - 2 ∧
    ∀ u : ℕ, ovF N t (edgeC N c1 c2) u + indN t c1 (u : Fin N) + indN t c2 (u : Fin N) = 3 * t := by
  have hN0 : 0 < N := by omega
  have hws : ∀ w ∈ [N + c1.val, N + c2.val], w < N + N := by
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · have := c1.isLt; omega
    · have := c2.isLt; omega
  have hleg := orChain_legal N 0 [N + c1.val, N + c2.val] (by omega) hws
  have hP : ∀ x y : Fin N, (edgeC N c1 c2).eval (oneEach x y) = true ↔
      (x ∈ ({0} : Finset (Fin N)) ∨ y ∈ ({c1, c2} : Finset (Fin N))) := by
    intro x y
    unfold edgeC
    rw [orChain_eval (N + N) 0 _ (by omega) hws (oneEach x y) (oneEach_length x y)]
    simp only [List.any_cons, List.any_nil, Bool.or_false]
    rw [oneEach_getD_left x y 0 hN0, oneEach_getD_right x y c1.val c1.isLt,
      oneEach_getD_right x y c2.val c2.isLt]
    simp only [Bool.or_eq_true, decide_eq_true_eq, Finset.mem_singleton, Finset.mem_insert,
      Fin.ext_iff, Fin.val_zero]
    constructor <;> intro h <;> omega
  refine ⟨hleg, by simp [edgeC, orChain_size], ?_, ?_⟩
  · have h := area_formula (fun z => (edgeC N c1 c2).eval (oneEach z.1 z.2)) {0} {c1, c2}
      (fun x y => hP x y)
    rw [Finset.card_singleton, Finset.card_pair hne] at h
    have h' : areaF N (edgeC N c1 c2) + 1 * 2 = (1 + 2) * N := h
    omega
  · intro u
    have h := ov_formula ht (fun z => (edgeC N c1 c2).eval (oneEach z.1 z.2)) {0} {c1, c2}
      (fun x y => hP x y) u
    rw [Finset.card_singleton, Finset.card_pair hne, Finset.sum_singleton, Finset.sum_pair hne] at h
    have hind : ∀ (y : Fin N), (if targetI N t u 0 y = true then 1 else 0) = indN t y (u : Fin N) := by
      intro y
      simp only [indN, targetI_iff, sub_zero]
    rw [hind, hind] at h
    have h' : ovF N t (edgeC N c1 c2) u + (indN t c1 (u : Fin N) + indN t c2 (u : Fin N)) =
      (1 + 2) * t := h
    omega

lemma loss_real {t : ℕ} (ht : t ≤ N) (C : Circuit) (u : ℕ) (c1 c2 : Fin N)
    (hcol : ovF N t C u + indN t c1 (u : Fin N) + indN t c2 (u : Fin N) = 3 * t) :
    (lossF N t C u : ℝ) = (areaF N C : ℝ) + N * t - 6 * t +
      2 * (winR t (u : Fin N) c1 + winR t (u : Fin N) c2) := by
  have h1 := loss_ov ht C u
  have h1r : (lossF N t C u : ℝ) + 2 * ovF N t C u = areaF N C + N * t := by exact_mod_cast h1
  have h2r : (ovF N t C u : ℝ) + (indN t c1 (u : Fin N) : ℝ) + (indN t c2 (u : Fin N) : ℝ) =
      3 * t := by exact_mod_cast hcol
  have hw : ∀ c : Fin N, ((indN t c (u : Fin N) : ℕ) : ℝ) = winR t (u : Fin N) c := by
    intro c
    simp only [indN, winR]
    split_ifs <;> simp
  rw [hw, hw] at h2r
  linarith

lemma main : ∀ (N t : ℕ), 5 < N → N < 2*t → t ≤ N →
  let X := Fin N
  let Circ := PEqualNP.CircuitLowerBounds.Circuit
  let legal := fun (C : Circ) =>
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (N+N) C ∧ C.output < N+N+C.size ∧
    ∀ gate ∈ C.gates, gate.inputs.length ≤ 2 ∧
      (gate.op = .and ∨ gate.op = .or ∨ (gate.op = .not ∧ gate.inputs.length = 1))
  let table := fun (C : Circ) (x y : X) => C.eval (PEqualNP.Represents.oneEach x y)
  let area := fun (C : Circ) =>
    ((Finset.univ : Finset (X × X)).filter (fun z => table C z.1 z.2 = true)).card
  let loss := fun (C : Circ) (u : ℕ) =>
    ((Finset.univ : Finset (X × X)).filter (fun z => table C z.1 z.2 ≠
      decide ((z.2.val + N - z.1.val + N - u % N) % N < t))).card
  let A := 3*N-2
  let bench := N*(N*t)-(2*t-N)*A
  let L := N/Nat.gcd N t
  let least := if L=1 then 1 else if L % 2=0 then L/2 else (L+3)/2
  let fits := fun (C : Circ) => legal C ∧ C.size ≤ 2 ∧ area C ≤ A
  let prob := fun (M : ℕ) (w : Fin M → ℝ) => (∀ i, 0 ≤ w i) ∧ (∑ i, w i)=1
  (∀ M : ℕ,
    (∃ (D : Fin M → Circ) (w : Fin M → ℝ), (∀ i, fits (D i)) ∧ prob M w ∧
      ∀ u : X, (N : ℝ)*(∑ i, w i*(loss (D i) u.val : ℝ)) ≤ (bench : ℝ)) ↔ least ≤ M) ∧
  (N % 2=1 → ∀ D : Circ, fits D → area D = A →
    let optimal := fun (w : X → ℝ) => ∀ u : X,
      (N : ℝ)*(∑ v : X, w v*(loss D (u.val+N-v.val) : ℝ)) ≤ (bench : ℝ)
    let supp := fun (w : X → ℝ) =>
      (Finset.univ.filter (fun v : X => @decide (0 < w v) (Classical.propDecidable _))).card
    (∀ w : X → ℝ, prob N w →
      (optimal w ↔ ∀ u v : X, v.val=(u.val+t) % N → w v=w u)) ∧
    (∀ M : ℕ, (∃ w : X → ℝ, prob N w ∧ optimal w ∧ supp w ≤ M) ↔ L ≤ M)) := by
  intro N t hN hNt htN
  intro X Circ legal table area loss A bench L least fits prob
  haveI : NeZero N := ⟨by omega⟩
  have hN0 : 0 < N := by omega
  have h2tN : ((2 * t - N : ℕ) : ℝ) = 2 * t - N := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hAle : (2 * t - N) * A ≤ N * (N * t) := by
    have h1 : 2 * t - N ≤ t := by omega
    have h2 : A ≤ N * N := by
      show 3 * N - 2 ≤ N * N
      have : 3 * N ≤ N * N := Nat.mul_le_mul_right N (by omega)
      omega
    calc (2 * t - N) * A ≤ t * (N * N) := Nat.mul_le_mul h1 h2
      _ = N * (N * t) := by ring
  have hbench : (bench : ℝ) = N * (N * t) - (2 * t - N) * (A : ℝ) := by
    show ((N * (N * t) - (2 * t - N) * A : ℕ) : ℝ) = _
    rw [Nat.cast_sub hAle, Nat.cast_mul (2 * t - N) A, h2tN]
    push_cast
    ring
  have hsl : ∀ C, ∑ u : Fin N, (lossF N t C u.val : ℝ) =
      N * (N * t) - (2 * t - N) * (areaF N C : ℝ) := by
    intro C
    have := sum_lossF hNt htN C
    have h' : (∑ u : Fin N, (lossF N t C u.val : ℝ)) + ((2 * t - N : ℕ) : ℝ) * areaF N C =
        N * (N * t) := by exact_mod_cast this
    rw [h2tN] at h'
    linarith
  refine ⟨?_, ?_⟩
  · intro M
    constructor
    · rintro ⟨D, w, hfit, ⟨hw0, hw1⟩, hle⟩
      set F : Fin N → ℝ := fun u => ∑ i, w i * (lossF N t (D i) u.val : ℝ) with hFdef
      have hsumF : ∑ u, F u = ∑ i, w i * ∑ u : Fin N, (lossF N t (D i) u.val : ℝ) := by
        simp only [hFdef, Finset.mul_sum]
        rw [Finset.sum_comm]
      have hgap : ∑ u, F u - bench = ∑ i, w i * ((2 * t - N) * ((A : ℝ) - areaF N (D i))) := by
        rw [hsumF, hbench]
        simp only [hsl]
        have e : ∑ i, w i * ((N : ℝ) * (N * t) - (2 * t - N) * A) = N * (N * t) - (2 * t - N) * A := by
          rw [← Finset.sum_mul, hw1, one_mul]
        rw [← e, ← Finset.sum_sub_distrib]
        apply sum_congr rfl
        intro i _
        ring
      have h2tNpos : (0 : ℝ) < 2 * t - N := by
        have : (N : ℝ) < 2 * t := by exact_mod_cast hNt
        linarith
      have hterm : ∀ i, 0 ≤ w i * ((2 * t - N) * ((A : ℝ) - areaF N (D i))) := by
        intro i
        have hai : (areaF N (D i) : ℝ) ≤ A := by exact_mod_cast (hfit i).2.2
        exact mul_nonneg (hw0 i) (mul_nonneg h2tNpos.le (by linarith))
      have hle' : ∀ u : Fin N, (N : ℝ) * F u ≤ bench := hle
      have hSumF : ∑ u, F u = bench := by
        have h1 : ∑ u, (N : ℝ) * F u ≤ ∑ _u : Fin N, (bench : ℝ) :=
          Finset.sum_le_sum (fun u _ => hle' u)
        rw [← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul] at h1
        have h2 : ∑ u, F u ≤ bench := le_of_mul_le_mul_left h1 (by exact_mod_cast hN0)
        have h3 : 0 ≤ ∑ i, w i * ((2 * t - N) * ((A : ℝ) - areaF N (D i))) :=
          sum_nonneg (fun i _ => hterm i)
        linarith
      have hareaA : ∀ i, 0 < w i → areaF N (D i) = A := by
        have hz : ∑ i, w i * ((2 * t - N) * ((A : ℝ) - areaF N (D i))) = 0 := by linarith
        rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hterm i)] at hz
        intro i hi
        have h0 := hz i (mem_univ _)
        rcases mul_eq_zero.mp h0 with h | h
        · linarith
        · rcases mul_eq_zero.mp h with h' | h'
          · linarith
          · have : (areaF N (D i) : ℝ) = A := by linarith
            exact_mod_cast this
      have hflat := (avg_iff F bench hSumF).mp hle'
      have hcol : ∀ i, ∃ c1 c2 : Fin N, c1 ≠ c2 ∧ (0 < w i → ∀ u : ℕ,
          ovF N t (D i) u + indN t c1 (u : Fin N) + indN t c2 (u : Fin N) = 3 * t) := by
        intro i
        by_cases hi : 0 < w i
        · obtain ⟨c1, c2, hne, h⟩ := colours_circ hN htN (D i) (hfit i).1 (hfit i).2.1
            (hareaA i hi)
          exact ⟨c1, c2, hne, fun _ => h⟩
        · exact ⟨0, 1, zero_ne_one_fin (by omega), fun h => absurd h hi⟩
      choose c1 c2 hne hcol using hcol
      have hFform : ∀ u : Fin N, F u = ((A : ℝ) + N * t - 6 * t) + 2 * Sw t (mass c1 c2 w) u := by
        intro u
        rw [← mass_Sw]
        have hi : ∀ i, w i * (lossF N t (D i) u.val : ℝ) = w i * ((A : ℝ) + N * t - 6 * t) +
            2 * (w i * (winR t u (c1 i) + winR t u (c2 i))) := by
          intro i
          by_cases hi : 0 < w i
          · rw [loss_real htN (D i) u.val (c1 i) (c2 i) (hcol i hi u.val), hareaA i hi,
              Fin.cast_val_eq_self]
            ring
          · have : w i = 0 := le_antisymm (not_lt.mp hi) (hw0 i)
            simp [this]
        simp only [hFdef]
        rw [Finset.sum_congr rfl (fun i _ => hi i), Finset.sum_add_distrib, ← Finset.sum_mul, hw1,
          ← Finset.mul_sum]
        ring
      have hper : ∀ d, mass c1 c2 w (d + (t : Fin N)) = mass c1 c2 w d := by
        rw [← window_iff htN]
        intro u
        have h1 := hflat u
        rw [hFform, hFform] at h1
        linarith
      exact clb htN hNt M c1 c2 hne w hw0 hw1 hper
    · intro hM
      obtain ⟨c1, c2, w, hne, hw0, hw1, hper⟩ := con (t := t) (by omega : 1 < N) htN hNt M hM
      have hD : ∀ i, ∃ C : Circuit, fits C ∧ areaF N C = A ∧ ∀ u : ℕ,
          ovF N t C u + indN t (c1 i) (u : Fin N) + indN t (c2 i) (u : Fin N) = 3 * t := by
        intro i
        obtain ⟨hleg, hsz, har, hov⟩ := edgeC_props (t := t) hN htN (c1 i) (c2 i) (hne i)
        exact ⟨edgeC N (c1 i) (c2 i), ⟨hleg, hsz, le_of_eq har⟩, har, hov⟩
      choose D hDfit hDarea hDcol using hD
      refine ⟨D, w, hDfit, ⟨hw0, hw1⟩, ?_⟩
      set F : Fin N → ℝ := fun u => ∑ i, w i * (lossF N t (D i) u.val : ℝ) with hFdef
      have hsumF : ∑ u, F u = ∑ i, w i * ∑ u : Fin N, (lossF N t (D i) u.val : ℝ) := by
        simp only [hFdef, Finset.mul_sum]
        rw [Finset.sum_comm]
      have hFform : ∀ u : Fin N, F u = ((A : ℝ) + N * t - 6 * t) + 2 * Sw t (mass c1 c2 w) u := by
        intro u
        rw [← mass_Sw]
        have hi : ∀ i, w i * (lossF N t (D i) u.val : ℝ) = w i * ((A : ℝ) + N * t - 6 * t) +
            2 * (w i * (winR t u (c1 i) + winR t u (c2 i))) := by
          intro i
          rw [loss_real htN (D i) u.val (c1 i) (c2 i) (hDcol i u.val), hDarea i,
            Fin.cast_val_eq_self]
          ring
        simp only [hFdef]
        rw [Finset.sum_congr rfl (fun i _ => hi i), Finset.sum_add_distrib, ← Finset.sum_mul, hw1,
          ← Finset.mul_sum]
        ring
      have hS := (window_iff htN (mass c1 c2 w)).mpr hper
      have hflat : ∀ u, F u = F 0 := by
        intro u
        rw [hFform, hFform, hS u]
      have hSumF : ∑ u, F u = bench := by
        rw [hsumF, hbench]
        simp only [hsl, hDarea]
        rw [← Finset.sum_mul, hw1, one_mul]
      exact (avg_iff F bench hSumF).mpr hflat
  · intro hodd D hfit hareaD optimal supp
    have hareaD' : areaF N D = A := hareaD
    obtain ⟨c1, c2, _, hcol⟩ := colours_circ (t := t) hN htN D hfit.1 hfit.2.1 hareaD
    have hcast : ∀ u v : Fin N, (((u.val + N - v.val : ℕ)) : Fin N) = u - v := by
      intro u v
      apply Fin.ext
      rw [Fin.val_natCast, Fin.val_sub]
      congr 1
      have := v.isLt
      omega
    have hopt : ∀ w : X → ℝ, prob N w → (optimal w ↔ ∀ e : Fin N, w (e + (t : Fin N)) = w e) := by
      intro w hw
      set F : Fin N → ℝ := fun u => ∑ v, w v * (lossF N t D (u.val + N - v.val) : ℝ) with hFdef
      have hFform : ∀ u, F u = ((A : ℝ) + N * t - 6 * t) +
          2 * Sw t (mass (fun v => c1 + v) (fun v => c2 + v) w) u := by
        intro u
        rw [← mass_Sw]
        have hi : ∀ v, w v * (lossF N t D (u.val + N - v.val) : ℝ) =
            w v * ((A : ℝ) + N * t - 6 * t) + 2 * (w v * (winR t u (c1 + v) + winR t u (c2 + v))) := by
          intro v
          rw [loss_real htN D _ c1 c2 (hcol _), hareaD', hcast]
          have e : ∀ c : Fin N, winR t (u - v) c = winR t u (c + v) := by
            intro c
            simp only [winR]
            rw [show c - (u - v) = c + v - u by ring]
          rw [e, e]
          ring
        simp only [hFdef]
        rw [Finset.sum_congr rfl (fun v _ => hi v), Finset.sum_add_distrib, ← Finset.sum_mul, hw.2,
          ← Finset.mul_sum]
        ring
      have hsh : ∀ v : Fin N, ∑ u : Fin N, (lossF N t D (u.val + N - v.val) : ℝ) =
          ∑ u : Fin N, (lossF N t D u.val : ℝ) := by
        intro v
        have e1 : ∀ u : Fin N, lossF N t D (u.val + N - v.val) = lossF N t D (u - v).val := by
          intro u
          have h1 : (u.val + N - v.val) % N = (u - v).val := by
            rw [← Fin.val_natCast, hcast]
          rw [lossF_mod N t D (u.val + N - v.val), h1]
        simp only [e1]
        exact Fintype.sum_equiv (Equiv.subRight v) _ _ (fun u => rfl)
      have hSumF : ∑ u, F u = bench := by
        simp only [hFdef]
        rw [Finset.sum_comm]
        simp only [← Finset.mul_sum, hsh, hsl, hareaD']
        rw [hbench, ← Finset.sum_mul, hw.2, one_mul]
      have h1 : optimal w ↔ ∀ u, F u = F 0 := avg_iff F bench hSumF
      rw [h1, ← wper_odd hodd c1 c2 w, ← window_iff htN]
      constructor
      · intro h u
        have := h u
        rw [hFform, hFform] at this
        linarith
      · intro h u
        rw [hFform, hFform, h u]
    refine ⟨?_, ?_⟩
    · intro w hw
      rw [hopt w hw]
      have hv : ∀ u v : Fin N, v.val = (u.val + t) % N ↔ v = u + (t : Fin N) := by
        intro u v
        rw [Fin.ext_iff, Fin.val_add, Fin.val_natCast, Nat.add_mod_mod]
      constructor
      · intro h u v huv
        rw [(hv u v).mp huv]
        exact h u
      · intro h e
        exact h e (e + (t : Fin N)) ((hv e _).mpr rfl)
    · intro M
      constructor
      · rintro ⟨w, hw, hw_opt, hsupp⟩
        have hper := (hopt w hw).mp hw_opt
        obtain ⟨v, hv⟩ : ∃ v, 0 < w v := by
          by_contra h
          push_neg at h
          have : ∑ v, w v ≤ 0 := Finset.sum_nonpos (fun v _ => h v)
          linarith [hw.2]
        have hsub : orbF t v ⊆ Finset.univ.filter
            (fun v' : X => @decide (0 < w v') (Classical.propDecidable _)) := by
          intro e he
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq]
          rw [per_orb w hper v e he]
          exact hv
        have := Finset.card_le_card hsub
        rw [card_orbF] at this
        exact le_trans this hsupp
      · intro hLM
        have hLpos : 0 < L := L_pos
        have hLr : (0 : ℝ) < L := by exact_mod_cast hLpos
        set w0 : Fin N → ℝ := fun d => if d ∈ orbF t (0 : Fin N) then 1 / (L : ℝ) else 0 with hw0def
        have hprob : prob N w0 := by
          refine ⟨fun i => ?_, ?_⟩
          · simp only [hw0def]
            split_ifs <;> positivity
          · simp only [hw0def]
            rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, card_orbF, nsmul_eq_mul]
            field_simp
            rfl
        refine ⟨w0, hprob, (hopt w0 hprob).mpr ?_, ?_⟩
        · intro e
          by_cases he : e ∈ orbF t (0 : Fin N)
          · simp [hw0def, he, orbF_add he]
          · have : e + (t : Fin N) ∉ orbF t (0 : Fin N) := fun h => he (orbF_sub h)
            simp [hw0def, he, this]
        · have hsub : Finset.univ.filter
              (fun v' : X => @decide (0 < w0 v') (Classical.propDecidable _)) ⊆ orbF t (0 : Fin N) := by
            intro e he
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq] at he
            by_contra hn
            simp [hw0def, hn] at he
          have := Finset.card_le_card hsub
          rw [card_orbF] at this
          exact le_trans this hLM

end Circ2

end PEqualNP.Outside.L_meta_32588_aux

theorem PEqualNP.Outside.L_meta_32588 : ∀ (N t : ℕ), 5 < N → N < 2*t → t ≤ N →
  let X := Fin N
  let Circ := PEqualNP.CircuitLowerBounds.Circuit
  let legal := fun (C : Circ) =>
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (N+N) C ∧ C.output < N+N+C.size ∧
    ∀ gate ∈ C.gates, gate.inputs.length ≤ 2 ∧
      (gate.op = .and ∨ gate.op = .or ∨ (gate.op = .not ∧ gate.inputs.length = 1))
  let table := fun (C : Circ) (x y : X) => C.eval (PEqualNP.Represents.oneEach x y)
  let area := fun (C : Circ) =>
    ((Finset.univ : Finset (X × X)).filter (fun z => table C z.1 z.2 = true)).card
  let loss := fun (C : Circ) (u : ℕ) =>
    ((Finset.univ : Finset (X × X)).filter (fun z => table C z.1 z.2 ≠
      decide ((z.2.val + N - z.1.val + N - u % N) % N < t))).card
  let A := 3*N-2
  let bench := N*(N*t)-(2*t-N)*A
  let L := N/Nat.gcd N t
  let least := if L=1 then 1 else if L % 2=0 then L/2 else (L+3)/2
  let fits := fun (C : Circ) => legal C ∧ C.size ≤ 2 ∧ area C ≤ A
  let prob := fun (M : ℕ) (w : Fin M → ℝ) => (∀ i, 0 ≤ w i) ∧ (∑ i, w i)=1
  (∀ M : ℕ,
    (∃ (D : Fin M → Circ) (w : Fin M → ℝ), (∀ i, fits (D i)) ∧ prob M w ∧
      ∀ u : X, (N : ℝ)*(∑ i, w i*(loss (D i) u.val : ℝ)) ≤ (bench : ℝ)) ↔ least ≤ M) ∧
  (N % 2=1 → ∀ D : Circ, fits D → area D = A →
    let optimal := fun (w : X → ℝ) => ∀ u : X,
      (N : ℝ)*(∑ v : X, w v*(loss D (u.val+N-v.val) : ℝ)) ≤ (bench : ℝ)
    let supp := fun (w : X → ℝ) =>
      (Finset.univ.filter (fun v : X => @decide (0 < w v) (Classical.propDecidable _))).card
    (∀ w : X → ℝ, prob N w →
      (optimal w ↔ ∀ u v : X, v.val=(u.val+t) % N → w v=w u)) ∧
    (∀ M : ℕ, (∃ w : X → ℝ, prob N w ∧ optimal w ∧ supp w ≤ M) ↔ L ≤ M)) :=
  PEqualNP.Outside.L_meta_32588_aux.main
