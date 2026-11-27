import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_282_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

def ValidGate (g : Gate) : Prop :=
  ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) ∨
    (g.op = .not ∧ g.inputs.length = 1)

def wireStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_wireStep_length (gs : List Gate) (x : List Bool) :
    (gs.foldl wireStep x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, List.length_cons, ih, wireStep, List.length_append, List.length_nil]
    omega

lemma getD_append_left {α : Type} (l r : List α) (i : ℕ) (d : α) (h : i < l.length) :
    (l ++ r).getD i d = l.getD i d := by
  simp [List.getD, List.getElem?_append_left h]

lemma getD_append_right {α : Type} (l r : List α) (i : ℕ) (d : α) (h : l.length ≤ i) :
    (l ++ r).getD i d = r.getD (i - l.length) d := by
  simp [List.getD, List.getElem?_append_right h]

lemma foldl_wireStep_getD_lt (gs : List Gate) (base : List Bool) (w : ℕ) (hw : w < base.length) :
    (gs.foldl wireStep base).getD w false = base.getD w false := by
  induction gs generalizing base with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hw' : w < (wireStep base g).length := by simp [wireStep]; omega
    rw [ih (wireStep base g) hw']
    exact getD_append_left base _ w false hw

lemma gateAt_append_left (g1 g2 : List Gate) (j : ℕ) (hj : j < g1.length) :
    gateAt ⟨g1 ++ g2, 0⟩ j = gateAt ⟨g1, 0⟩ j := by
  unfold gateAt
  exact getD_append_left g1 g2 j _ hj

lemma gateAt_append_right (g1 g2 : List Gate) (j : ℕ) (hj : g1.length ≤ j) :
    gateAt ⟨g1 ++ g2, 0⟩ j = gateAt ⟨g2, 0⟩ (j - g1.length) := by
  unfold gateAt
  exact getD_append_right g1 g2 j _ hj

def remapWire (k base : ℕ) (inp : Fin k → Fin base) (i : ℕ) : ℕ :=
  if h : i < k then (inp ⟨i, h⟩).val else (i - k) + base

def remapGate (k base : ℕ) (inp : Fin k → Fin base) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (remapWire k base inp)⟩

lemma remapGate_valid {k base : ℕ} {inp : Fin k → Fin base} {g : Gate} (hv : ValidGate g) :
    ValidGate (remapGate k base inp g) := by
  rcases hv with ⟨hop, hlen⟩ | ⟨hop, hlen⟩
  · left; exact ⟨hop, by simp [remapGate, hlen]⟩
  · right; exact ⟨hop, by simp [remapGate, hlen]⟩

lemma gateAt_map {k base : ℕ} {inp : Fin k → Fin base} (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    gateAt ⟨gs.map (remapGate k base inp), 0⟩ j = remapGate k base inp (gateAt ⟨gs, 0⟩ j) := by
  unfold gateAt
  have hj' : j < (gs.map (remapGate k base inp)).length := by simp [hj]
  rw [List.getD_eq_getElem _ _ hj', List.getD_eq_getElem _ _ hj, List.getElem_map]

lemma readsBack_prefix {k : ℕ} (gs : List Gate) (g : Gate)
    (hrb : ReadsBack k ⟨gs ++ [g], 0⟩) :
    ReadsBack k ⟨gs, 0⟩ ∧ ∀ i ∈ g.inputs, i < k + gs.length := by
  constructor
  · intro j hj i hi
    dsimp only at hj
    have hj' : j < (gs ++ [g]).length := by simp; omega
    have h1 := hrb j hj' i
    rw [gateAt_append_left gs [g] j hj] at h1
    exact h1 hi
  · intro i hi
    have hj' : gs.length < (gs ++ [g]).length := by simp
    have h1 := hrb gs.length hj' i
    rw [gateAt_append_right gs [g] gs.length le_rfl] at h1
    simp only [Nat.sub_self, gateAt, List.getD_cons_zero] at h1
    exact h1 hi

lemma foldl_remap_eval {k base : ℕ} (inp : Fin k → Fin base)
    (w1 w2 : List Bool) (hw1 : w1.length = base) (hw2 : w2.length = k)
    (hinp : ∀ i : Fin k, w1.getD (inp i).val false = w2.getD i.val false)
    (gs : List Gate) (hrb : ReadsBack k ⟨gs, 0⟩) :
    ∀ i < k + gs.length,
      ((gs.map (remapGate k base inp)).foldl wireStep w1).getD (remapWire k base inp i) false =
        (gs.foldl wireStep w2).getD i false := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro i hi
    simp only [List.length_nil, Nat.add_zero] at hi
    simp only [List.map_nil, List.foldl_nil, remapWire, hi, ↓reduceDIte]
    exact hinp ⟨i, hi⟩
  | append_singleton gs g ih =>
    rcases readsBack_prefix gs g hrb with ⟨hrb_gs, hrb_g⟩
    have ih' := ih hrb_gs
    set u := gs.foldl wireStep w2 with hu
    set v := (gs.map (remapGate k base inp)).foldl wireStep w1 with hv
    have hulen : u.length = k + gs.length := by
      rw [hu, foldl_wireStep_length, hw2]
    have hvlen : v.length = base + gs.length := by
      rw [hv, foldl_wireStep_length, hw1, List.length_map]
    have hbit : (remapGate k base inp g).op.eval
        ((remapGate k base inp g).inputs.map fun r => v.getD r false) =
        g.op.eval (g.inputs.map fun idx => u.getD idx false) := by
      simp only [remapGate, List.map_map]
      congr 1
      apply List.map_congr_left
      intro idx hidx
      exact ih' idx (hrb_g idx hidx)
    intro i hi
    simp only [List.length_append, List.length_cons, List.length_nil] at hi
    simp only [List.map_append, List.map_cons, List.map_nil, List.foldl_append,
      List.foldl_cons, List.foldl_nil]
    change (wireStep v (remapGate k base inp g)).getD (remapWire k base inp i) false =
      (wireStep u g).getD i false
    by_cases hilt : i < k + gs.length
    · have hrl : remapWire k base inp i < v.length := by
        unfold remapWire
        split_ifs with hik
        · have := (inp ⟨i, hik⟩).isLt; omega
        · omega
      unfold wireStep
      rw [getD_append_left v _ _ false hrl, getD_append_left u _ _ false (by omega)]
      exact ih' i hilt
    · have hieq : i = k + gs.length := by omega
      subst hieq
      have hge : ¬ (k + gs.length < k) := by omega
      have hrm : remapWire k base inp (k + gs.length) = v.length := by
        simp only [remapWire, hge, ↓reduceDIte]
        omega
      unfold wireStep
      rw [hrm, getD_append_right v _ v.length false le_rfl, Nat.sub_self, List.getD_cons_zero]
      rw [show k + gs.length = u.length by omega,
        getD_append_right u _ u.length false le_rfl, Nat.sub_self, List.getD_cons_zero]
      exact hbit

def HasCirc (n m B : ℕ) (f : (Fin n → Bool) → (Fin m → Bool)) : Prop :=
  ∃ (C : Circuit) (out : Fin m → Fin (n + C.size)),
    ReadsBack n C ∧ (∀ g ∈ C.gates, ValidGate g) ∧ C.size ≤ B ∧
    ∀ x : Fin n → Bool, ∀ j : Fin m,
      (C.wires (List.ofFn x)).getD (out j).val false = f x j

lemma HasCirc.weaken {n m B₁ B₂ : ℕ} {f : (Fin n → Bool) → (Fin m → Bool)}
    (hle : B₁ ≤ B₂) (h : HasCirc n m B₁ f) : HasCirc n m B₂ f := by
  rcases h with ⟨C, out, rb, vg, sz, ev⟩
  exact ⟨C, out, rb, vg, le_trans sz hle, ev⟩

lemma HasCirc.congr {n m B : ℕ} {f g : (Fin n → Bool) → (Fin m → Bool)}
    (heq : ∀ x j, f x j = g x j) (h : HasCirc n m B f) : HasCirc n m B g := by
  rcases h with ⟨C, out, rb, vg, sz, ev⟩
  exact ⟨C, out, rb, vg, sz, fun x j => by rw [ev x j, heq x j]⟩

lemma HasCirc.proj {n m : ℕ} (idx : Fin m → Fin n) :
    HasCirc n m 0 (fun x j => x (idx j)) := by
  refine ⟨⟨[], 0⟩, fun j => ⟨(idx j).val, by simp [Circuit.size]⟩, ?_, ?_, by simp [Circuit.size], ?_⟩
  · intro j hj; simp at hj
  · intro g hg; simp at hg
  · intro x j
    change (List.ofFn x).getD (idx j).val false = x (idx j)
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]

lemma HasCirc.comp {n k m B₁ B₂ : ℕ}
    {f : (Fin n → Bool) → (Fin k → Bool)} {g : (Fin k → Bool) → (Fin m → Bool)}
    (h1 : HasCirc n k B₁ f) (h2 : HasCirc k m B₂ g) :
    HasCirc n m (B₁ + B₂) (fun x => g (f x)) := by
  rcases h1 with ⟨C1, out1, rb1, vg1, sz1, ev1⟩
  rcases h2 with ⟨C2, out2, rb2, vg2, sz2, ev2⟩
  let base := n + C1.size
  let gs2 := C2.gates.map (remapGate k base out1)
  let C : Circuit := ⟨C1.gates ++ gs2, 0⟩
  have hCsize : C.size = C1.size + C2.size := by
    simp [C, Circuit.size, gs2]
  have hout_lt : ∀ j : Fin m, remapWire k base out1 (out2 j).val < n + C.size := by
    intro j
    unfold remapWire
    split_ifs with hi
    · have := (out1 ⟨(out2 j).val, hi⟩).isLt; omega
    · have := (out2 j).isLt; dsimp [base]; omega
  refine ⟨C, fun j => ⟨remapWire k base out1 (out2 j).val, hout_lt j⟩, ?_, ?_, ?_, ?_⟩
  · intro j hj i hi
    simp only [C, List.length_append, gs2, List.length_map] at hj
    by_cases hj1 : j < C1.gates.length
    · rw [gateAt_append_left C1.gates gs2 j hj1] at hi
      exact rb1 j hj1 i hi
    · rw [gateAt_append_right C1.gates gs2 j (by omega)] at hi
      have hj2 : j - C1.gates.length < C2.gates.length := by omega
      rw [gateAt_map C2.gates (j - C1.gates.length) hj2] at hi
      simp only [remapGate, List.mem_map] at hi
      rcases hi with ⟨i0, hi0, rfl⟩
      have hi0lt : i0 < k + (j - C1.gates.length) := rb2 (j - C1.gates.length) hj2 i0 hi0
      unfold remapWire
      split_ifs with hik
      · have := (out1 ⟨i0, hik⟩).isLt
        have : C1.size = C1.gates.length := rfl
        omega
      · have : C1.size = C1.gates.length := rfl
        dsimp [base]
        omega
  · intro gt hgt
    simp only [C, List.mem_append, gs2, List.mem_map] at hgt
    rcases hgt with h | ⟨g0, hg0, rfl⟩
    · exact vg1 gt h
    · exact remapGate_valid (vg2 g0 hg0)
  · rw [hCsize]; omega
  · intro x j
    change ((C1.gates ++ gs2).foldl wireStep (List.ofFn x)).getD (remapWire k base out1 (out2 j).val) false =
      g (f x) j
    rw [List.foldl_append]
    have hw1 : (C1.gates.foldl wireStep (List.ofFn x)).length = base := by
      rw [foldl_wireStep_length, List.length_ofFn]; rfl
    have hw2 : (List.ofFn (f x)).length = k := List.length_ofFn
    have hinp : ∀ i : Fin k,
        (C1.gates.foldl wireStep (List.ofFn x)).getD (out1 i).val false =
        (List.ofFn (f x)).getD i.val false := by
      intro i
      rw [show C1.gates.foldl wireStep (List.ofFn x) = C1.wires (List.ofFn x) from rfl, ev1 x i]
      rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
    have hrem := foldl_remap_eval out1 (C1.gates.foldl wireStep (List.ofFn x)) (List.ofFn (f x))
      hw1 hw2 hinp C2.gates rb2 (out2 j).val (out2 j).isLt
    rw [hrem]
    exact ev2 (f x) j

lemma HasCirc.pair {n m₁ m₂ B₁ B₂ : ℕ}
    {f₁ : (Fin n → Bool) → (Fin m₁ → Bool)} {f₂ : (Fin n → Bool) → (Fin m₂ → Bool)}
    (h1 : HasCirc n m₁ B₁ f₁) (h2 : HasCirc n m₂ B₂ f₂) :
    HasCirc n (m₁ + m₂) (B₁ + B₂) (fun x => Fin.append (f₁ x) (f₂ x)) := by
  rcases h1 with ⟨C1, out1, rb1, vg1, sz1, ev1⟩
  rcases h2 with ⟨C2, out2, rb2, vg2, sz2, ev2⟩
  let base := n + C1.size
  let idOut : Fin n → Fin base := fun i => ⟨i.val, by dsimp [base]; omega⟩
  let gs2 := C2.gates.map (remapGate n base idOut)
  let C : Circuit := ⟨C1.gates ++ gs2, 0⟩
  have hCsize : C.size = C1.size + C2.size := by simp [C, Circuit.size, gs2]
  have hout2_lt : ∀ j : Fin m₂, remapWire n base idOut (out2 j).val < n + C.size := by
    intro j
    unfold remapWire
    split_ifs with hi
    · dsimp [idOut]; omega
    · have := (out2 j).isLt; dsimp [base]; omega
  let out : Fin (m₁ + m₂) → Fin (n + C.size) :=
    Fin.addCases (fun j => ⟨(out1 j).val, by have := (out1 j).isLt; omega⟩)
      (fun j => ⟨remapWire n base idOut (out2 j).val, hout2_lt j⟩)
  refine ⟨C, out, ?_, ?_, ?_, ?_⟩
  · intro j hj i hi
    simp only [C, List.length_append, gs2, List.length_map] at hj
    by_cases hj1 : j < C1.gates.length
    · rw [gateAt_append_left C1.gates gs2 j hj1] at hi
      exact rb1 j hj1 i hi
    · rw [gateAt_append_right C1.gates gs2 j (by omega)] at hi
      have hj2 : j - C1.gates.length < C2.gates.length := by omega
      rw [gateAt_map C2.gates (j - C1.gates.length) hj2] at hi
      simp only [remapGate, List.mem_map] at hi
      rcases hi with ⟨i0, hi0, rfl⟩
      have hi0lt : i0 < n + (j - C1.gates.length) := rb2 (j - C1.gates.length) hj2 i0 hi0
      unfold remapWire
      split_ifs with hik
      · dsimp [idOut]; omega
      · have : C1.size = C1.gates.length := rfl; dsimp [base]; omega
  · intro gt hgt
    simp only [C, List.mem_append, gs2, List.mem_map] at hgt
    rcases hgt with h | ⟨g0, hg0, rfl⟩
    · exact vg1 gt h
    · exact remapGate_valid (vg2 g0 hg0)
  · rw [hCsize]; omega
  · intro x j
    refine Fin.addCases ?_ ?_ j
    · intro j1
      dsimp only [out]
      rw [Fin.addCases_left, Fin.append_left]
      change ((C1.gates ++ gs2).foldl wireStep (List.ofFn x)).getD (out1 j1).val false = f₁ x j1
      rw [List.foldl_append]
      have hlen : (C1.gates.foldl wireStep (List.ofFn x)).length = n + C1.size := by
        rw [foldl_wireStep_length, List.length_ofFn]; rfl
      rw [foldl_wireStep_getD_lt gs2 _ _ (by rw [hlen]; exact (out1 j1).isLt)]
      exact ev1 x j1
    · intro j2
      dsimp only [out]
      rw [Fin.addCases_right, Fin.append_right]
      change ((C1.gates ++ gs2).foldl wireStep (List.ofFn x)).getD
        (remapWire n base idOut (out2 j2).val) false = f₂ x j2
      rw [List.foldl_append]
      have hw1 : (C1.gates.foldl wireStep (List.ofFn x)).length = base := by
        rw [foldl_wireStep_length, List.length_ofFn]; rfl
      have hw2 : (List.ofFn x).length = n := List.length_ofFn
      have hinp : ∀ i : Fin n,
          (C1.gates.foldl wireStep (List.ofFn x)).getD (idOut i).val false =
          (List.ofFn x).getD i.val false := by
        intro i
        dsimp [idOut]
        exact foldl_wireStep_getD_lt C1.gates (List.ofFn x) i.val (by rw [List.length_ofFn]; exact i.isLt)
      have hrem := foldl_remap_eval idOut (C1.gates.foldl wireStep (List.ofFn x)) (List.ofFn x)
        hw1 hw2 hinp C2.gates rb2 (out2 j2).val (out2 j2).isLt
      rw [hrem]
      exact ev2 x j2

lemma HasCirc.vec {n m : ℕ} {B : Fin m → ℕ} {f : (Fin n → Bool) → (Fin m → Bool)}
    (hf : ∀ j : Fin m, HasCirc n 1 (B j) (fun x _ => f x j)) :
    HasCirc n m (∑ j : Fin m, B j) f := by
  induction m with
  | zero =>
    simpa using (HasCirc.proj (n := n) (m := 0) Fin.elim0).congr (fun x j => Fin.elim0 j)
  | succ m ih =>
    have hpre := ih (B := fun j => B j.castSucc) (f := fun x j => f x j.castSucc)
      (fun j => hf j.castSucc)
    have hlast := hf (Fin.last m)
    have hp := HasCirc.pair hpre hlast
    rw [Fin.sum_univ_castSucc]
    refine hp.congr ?_
    intro x j
    refine Fin.lastCases ?_ ?_ j
    · change Fin.append _ _ (Fin.natAdd m ⟨0, by omega⟩) = f x (Fin.last m)
      rw [Fin.append_right]
    · intro j'
      change Fin.append _ _ (Fin.castAdd 1 j') = f x j'.castSucc
      rw [Fin.append_left]

lemma HasCirc.vecConst {n m B : ℕ} {f : (Fin n → Bool) → (Fin m → Bool)}
    (hf : ∀ j : Fin m, HasCirc n 1 B (fun x _ => f x j)) :
    HasCirc n m (m * B) f := by
  have h := HasCirc.vec (B := fun _ : Fin m => B) hf
  simpa using h

lemma div_lt_of_lt_mul_right {a b c : ℕ} (h : a < b * c) : a / c < b :=
  Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact h)

lemma HasCirc.finBlocks {n q w B : ℕ} (hw : 0 < w)
    {f : Fin q → (Fin n → Bool) → (Fin w → Bool)}
    (hf : ∀ b : Fin q, HasCirc n w B (f b)) :
    HasCirc n (q * w) (q * B) (fun x j =>
      f ⟨j.val / w, div_lt_of_lt_mul_right j.isLt⟩ x ⟨j.val % w, Nat.mod_lt _ hw⟩) := by
  induction q with
  | zero =>
    refine (HasCirc.proj (n := n) (m := 0 * w) (fun j =>
      Fin.elim0 (finCongr (Nat.zero_mul w) j))).weaken (by omega) |>.congr ?_
    intro x j
    exact Fin.elim0 (finCongr (Nat.zero_mul w) j)
  | succ q ih =>
    have h1 := ih (f := fun b => f b.castSucc) (fun b => hf b.castSucc)
    have h2 := hf (Fin.last q)
    have hp := HasCirc.pair h1 h2
    have hcast : (q + 1) * w = q * w + w := by ring
    have hB : (q + 1) * B = q * B + B := by ring
    rw [hB]
    have hproj : HasCirc (q * w + w) ((q + 1) * w) 0
        (fun y j => y ⟨j.val, by omega⟩) := HasCirc.proj _
    refine (HasCirc.comp hp hproj).weaken (by omega) |>.congr ?_
    intro x j
    by_cases hlt : j.val < q * w
    · have hcast_eq : (⟨j.val, by omega⟩ : Fin (q * w + w)) = Fin.castAdd w ⟨j.val, hlt⟩ := rfl
      rw [hcast_eq, Fin.append_left]
      rfl
    · have hge : q * w ≤ j.val := by omega
      have hsub : j.val - q * w < w := by omega
      have hcast_eq : (⟨j.val, by omega⟩ : Fin (q * w + w)) =
          Fin.natAdd (q * w) ⟨j.val - q * w, hsub⟩ := by
        apply Fin.ext; simp [Fin.natAdd]; omega
      rw [hcast_eq, Fin.append_right]
      have hdiv : j.val / w = q :=
        Nat.div_eq_of_lt_le hge (by have := j.isLt; linarith)
      have hmod : j.val % w = j.val - q * w := by
        have hdm := Nat.div_add_mod j.val w
        rw [hdiv] at hdm
        have : w * q = q * w := Nat.mul_comm w q
        omega
      congr 1
      · apply Fin.ext; simp [Fin.last, hdiv]
      · apply Fin.ext; exact hmod.symm

lemma HasCirc.foldl {n s B₀ B₁ : ℕ} {init : (Fin n → Bool) → (Fin s → Bool)}
    (hinit : HasCirc n s B₀ init)
    (steps : ℕ)
    (step : Fin steps → (Fin (n + s) → Bool) → (Fin s → Bool))
    (hstep : ∀ i : Fin steps, HasCirc (n + s) s B₁ (step i)) :
    HasCirc n s (B₀ + steps * B₁) (fun x =>
      (List.finRange steps).foldl (fun st i => step i (Fin.append x st)) (init x)) := by
  induction steps with
  | zero =>
    simpa using hinit
  | succ steps ih =>
    have hpre := ih (fun i => step i.castSucc) (fun i => hstep i.castSucc)
    have hid : HasCirc n n 0 (fun x => x) := HasCirc.proj id
    have hpair := HasCirc.pair hid hpre
    have hcomp := HasCirc.comp hpair (hstep (Fin.last steps))
    have hbudget : 0 + (B₀ + steps * B₁) + B₁ = B₀ + (steps + 1) * B₁ := by ring
    rw [← hbudget]
    refine hcomp.congr ?_
    intro x j
    rw [List.finRange_succ_last, List.foldl_append, List.foldl_cons, List.foldl_nil, List.foldl_map]

lemma append_fin1_0 {a b : Fin 1 → Bool} :
    Fin.append a b (0 : Fin 2) = a 0 := by
  change Fin.append a b (Fin.castAdd 1 0) = a 0
  rw [Fin.append_left]

lemma append_fin1_1 {a b : Fin 1 → Bool} :
    Fin.append a b (1 : Fin 2) = b 0 := by
  change Fin.append a b (Fin.natAdd 1 0) = b 0
  rw [Fin.append_right]

lemma HasCirc.notGate : HasCirc 1 1 1 (fun x _ => !(x 0)) := by
  refine ⟨⟨[⟨.not, [0]⟩], 0⟩, fun _ => ⟨1, by simp [Circuit.size]⟩, ?_, ?_, by simp [Circuit.size], ?_⟩
  · intro j hj i hi
    simp only [List.length_cons, List.length_nil] at hj
    have hj0 : j = 0 := by omega
    subst hj0
    simp [gateAt] at hi
    omega
  · intro g hg; simp at hg; subst hg; right; simp
  · intro x j
    simp [Circuit.wires, GateOp.eval]

lemma HasCirc.andGate : HasCirc 2 1 1 (fun x _ => x 0 && x 1) := by
  refine ⟨⟨[⟨.and, [0, 1]⟩], 0⟩, fun _ => ⟨2, by simp [Circuit.size]⟩, ?_, ?_, by simp [Circuit.size], ?_⟩
  · intro j hj i hi
    simp only [List.length_cons, List.length_nil] at hj
    have hj0 : j = 0 := by omega
    subst hj0
    simp [gateAt] at hi
    omega
  · intro g hg; simp at hg; subst hg; left; simp
  · intro x j
    simp [Circuit.wires, GateOp.eval]

lemma HasCirc.orGate : HasCirc 2 1 1 (fun x _ => x 0 || x 1) := by
  refine ⟨⟨[⟨.or, [0, 1]⟩], 0⟩, fun _ => ⟨2, by simp [Circuit.size]⟩, ?_, ?_, by simp [Circuit.size], ?_⟩
  · intro j hj i hi
    simp only [List.length_cons, List.length_nil] at hj
    have hj0 : j = 0 := by omega
    subst hj0
    simp [gateAt] at hi
    omega
  · intro g hg; simp at hg; subst hg; left; simp
  · intro x j
    simp [Circuit.wires, GateOp.eval]

lemma HasCirc.const {n : ℕ} (hn : 0 < n) (b : Bool) :
    HasCirc n 1 2 (fun _ _ => b) := by
  have hx0 : HasCirc n 1 0 (fun x _ => x ⟨0, hn⟩) := HasCirc.proj (fun _ => ⟨0, hn⟩)
  have hnx0 : HasCirc n 1 1 (fun x _ => !(x ⟨0, hn⟩)) :=
    (HasCirc.comp hx0 HasCirc.notGate).weaken (by omega)
  have hp := HasCirc.pair hx0 hnx0
  cases b with
  | false =>
    refine (HasCirc.comp hp HasCirc.andGate).weaken (by omega) |>.congr ?_
    intro x _
    rw [append_fin1_0, append_fin1_1]
    simp
  | true =>
    refine (HasCirc.comp hp HasCirc.orGate).weaken (by omega) |>.congr ?_
    intro x _
    rw [append_fin1_0, append_fin1_1]
    simp

lemma HasCirc.not1 {n B : ℕ} {f : (Fin n → Bool) → Bool}
    (hf : HasCirc n 1 B (fun x _ => f x)) :
    HasCirc n 1 (B + 1) (fun x _ => !(f x)) :=
  HasCirc.comp hf HasCirc.notGate

lemma HasCirc.and2 {n B₁ B₂ : ℕ} {f₁ f₂ : (Fin n → Bool) → Bool}
    (h1 : HasCirc n 1 B₁ (fun x _ => f₁ x)) (h2 : HasCirc n 1 B₂ (fun x _ => f₂ x)) :
    HasCirc n 1 (B₁ + B₂ + 1) (fun x _ => f₁ x && f₂ x) := by
  refine (HasCirc.comp (HasCirc.pair h1 h2) HasCirc.andGate).congr ?_
  intro x _
  rw [append_fin1_0, append_fin1_1]

lemma HasCirc.or2 {n B₁ B₂ : ℕ} {f₁ f₂ : (Fin n → Bool) → Bool}
    (h1 : HasCirc n 1 B₁ (fun x _ => f₁ x)) (h2 : HasCirc n 1 B₂ (fun x _ => f₂ x)) :
    HasCirc n 1 (B₁ + B₂ + 1) (fun x _ => f₁ x || f₂ x) := by
  refine (HasCirc.comp (HasCirc.pair h1 h2) HasCirc.orGate).congr ?_
  intro x _
  rw [append_fin1_0, append_fin1_1]

lemma HasCirc.xorGate : HasCirc 2 1 4 (fun x _ => Bool.xor (x 0) (x 1)) := by
  have hx0 : HasCirc 2 1 0 (fun x _ => x 0) := HasCirc.proj (fun _ => 0)
  have hx1 : HasCirc 2 1 0 (fun x _ => x 1) := HasCirc.proj (fun _ => 1)
  have hor := HasCirc.or2 hx0 hx1
  have hnand := HasCirc.not1 (HasCirc.and2 hx0 hx1)
  refine (HasCirc.and2 hor hnand).weaken (by omega) |>.congr ?_
  intro x _
  cases x 0 <;> cases x 1 <;> rfl

lemma HasCirc.xor2 {n B₁ B₂ : ℕ} {f₁ f₂ : (Fin n → Bool) → Bool}
    (h1 : HasCirc n 1 B₁ (fun x _ => f₁ x)) (h2 : HasCirc n 1 B₂ (fun x _ => f₂ x)) :
    HasCirc n 1 (B₁ + B₂ + 4) (fun x _ => Bool.xor (f₁ x) (f₂ x)) := by
  refine (HasCirc.comp (HasCirc.pair h1 h2) HasCirc.xorGate).congr ?_
  intro x _
  rw [append_fin1_0, append_fin1_1]

lemma HasCirc.iteGate : HasCirc 3 1 4 (fun x _ => if x 0 then x 1 else x 2) := by
  have hs : HasCirc 3 1 0 (fun x _ => x 0) := HasCirc.proj (fun _ => 0)
  have ht : HasCirc 3 1 0 (fun x _ => x 1) := HasCirc.proj (fun _ => 1)
  have hf : HasCirc 3 1 0 (fun x _ => x 2) := HasCirc.proj (fun _ => 2)
  have h1 := HasCirc.and2 hs ht
  have h2 := HasCirc.and2 (HasCirc.not1 hs) hf
  refine (HasCirc.or2 h1 h2).weaken (by omega) |>.congr ?_
  intro x _
  cases x 0 <;> cases x 1 <;> cases x 2 <;> rfl

lemma HasCirc.ite3 {n B₀ B₁ B₂ : ℕ} {s t f : (Fin n → Bool) → Bool}
    (hs : HasCirc n 1 B₀ (fun x _ => s x))
    (ht : HasCirc n 1 B₁ (fun x _ => t x))
    (hf : HasCirc n 1 B₂ (fun x _ => f x)) :
    HasCirc n 1 (B₀ + B₁ + B₂ + 4) (fun x _ => if s x then t x else f x) := by
  have hp := HasCirc.pair (HasCirc.pair hs ht) hf
  refine (HasCirc.comp hp HasCirc.iteGate).weaken (by omega) |>.congr ?_
  intro x _
  have h0 : Fin.append (Fin.append (fun _ : Fin 1 => s x) (fun _ : Fin 1 => t x))
      (fun _ : Fin 1 => f x) (0 : Fin 3) = s x := by
    change Fin.append _ _ (Fin.castAdd 1 (0 : Fin 2)) = s x
    rw [Fin.append_left, append_fin1_0]
  have h1 : Fin.append (Fin.append (fun _ : Fin 1 => s x) (fun _ : Fin 1 => t x))
      (fun _ : Fin 1 => f x) (1 : Fin 3) = t x := by
    change Fin.append _ _ (Fin.castAdd 1 (1 : Fin 2)) = t x
    rw [Fin.append_left, append_fin1_1]
  have h2 : Fin.append (Fin.append (fun _ : Fin 1 => s x) (fun _ : Fin 1 => t x))
      (fun _ : Fin 1 => f x) (2 : Fin 3) = f x := by
    change Fin.append _ _ (Fin.natAdd 2 (0 : Fin 1)) = f x
    rw [Fin.append_right]
  rw [h0, h1, h2]

lemma HasCirc.table1 (d : ℕ) (hd : 0 < d) (f : (Fin d → Bool) → Bool) :
    HasCirc d 1 (10 * 2 ^ d - 4) (fun x _ => f x) := by
  induction d with
  | zero => omega
  | succ d ih =>
    cases d with
    | zero =>
      cases h0 : f (fun _ => false) <;> cases h1 : f (fun _ => true)
      · refine (HasCirc.const (n := 1) (by omega) false).weaken (by omega) |>.congr ?_
        intro x _
        have hx : x = fun _ => x 0 := funext fun i => by fin_cases i; rfl
        rw [hx]; cases x 0 <;> [exact h0.symm; exact h1.symm]
      · refine (HasCirc.proj (n := 1) (m := 1) (fun _ => 0)).weaken (by omega) |>.congr ?_
        intro x _
        have hx : x = fun _ => x 0 := funext fun i => by fin_cases i; rfl
        rw [hx]; cases x 0 <;> simp [h0, h1]
      · refine HasCirc.notGate.weaken (by omega) |>.congr ?_
        intro x _
        have hx : x = fun _ => x 0 := funext fun i => by fin_cases i; rfl
        rw [hx]; cases x 0 <;> simp [h0, h1]
      · refine (HasCirc.const (n := 1) (by omega) true).weaken (by omega) |>.congr ?_
        intro x _
        have hx : x = fun _ => x 0 := funext fun i => by fin_cases i; rfl
        rw [hx]; cases x 0 <;> [exact h0.symm; exact h1.symm]
    | succ d' =>
      have hm : 0 < d' + 1 := by omega
      let fT : (Fin (d' + 1) → Bool) → Bool := fun y => f (Fin.cons true y)
      let fF : (Fin (d' + 1) → Bool) → Bool := fun y => f (Fin.cons false y)
      have hT := ih hm fT
      have hF := ih hm fF
      have htail : HasCirc (d' + 1 + 1) (d' + 1) 0 (fun x i => x i.succ) := HasCirc.proj Fin.succ
      have hT' := HasCirc.comp htail hT
      have hF' := HasCirc.comp htail hF
      have hs : HasCirc (d' + 1 + 1) 1 0 (fun x _ => x 0) := HasCirc.proj (fun _ => 0)
      have hite := HasCirc.ite3 hs hT' hF'
      have hbd : 0 + (0 + (10 * 2 ^ (d' + 1) - 4)) + (0 + (10 * 2 ^ (d' + 1) - 4)) + 4 ≤
          10 * 2 ^ (d' + 1 + 1) - 4 := by
        have h2 : 1 ≤ 2 ^ (d' + 1) := Nat.one_le_two_pow
        have hp : 2 ^ (d' + 1 + 1) = 2 * 2 ^ (d' + 1) := by rw [pow_succ]; ring
        omega
      refine hite.weaken hbd |>.congr ?_
      intro x _
      have hx : x = Fin.cons (x 0) (fun i => x i.succ) := by
        funext i; refine Fin.cases rfl (fun _ => rfl) i
      cases hx0 : x 0
      · simp only [Bool.false_eq_true, ↓reduceIte, fF]
        conv_rhs => rw [hx, hx0]
      · simp only [↓reduceIte, fT]
        conv_rhs => rw [hx, hx0]

lemma HasCirc.table (d m : ℕ) (hd : 0 < d) (f : (Fin d → Bool) → (Fin m → Bool)) :
    HasCirc d m (m * (10 * 2 ^ d)) f :=
  HasCirc.vecConst (fun j => (HasCirc.table1 d hd (fun x => f x j)).weaken (by omega))

lemma HasCirc.orList {n : ℕ} (hn : 0 < n) (l : List (Fin n)) :
    HasCirc n 1 (l.length + 2) (fun x _ => l.foldl (fun acc i => acc || x i) false) := by
  induction l using List.reverseRecOn with
  | nil =>
    simpa using HasCirc.const hn false
  | append_singleton l a ih =>
    have ha : HasCirc n 1 0 (fun x _ => x a) := HasCirc.proj (fun _ => a)
    have hor := HasCirc.or2 ih ha
    refine hor.weaken (by simp) |>.congr ?_
    intro x _
    simp [List.foldl_append]

lemma HasCirc.xorList {n : ℕ} (hn : 0 < n) (l : List (Fin n)) :
    HasCirc n 1 (4 * l.length + 2) (fun x _ => l.foldl (fun acc i => Bool.xor acc (x i)) false) := by
  induction l using List.reverseRecOn with
  | nil =>
    simpa using HasCirc.const hn false
  | append_singleton l a ih =>
    have ha : HasCirc n 1 0 (fun x _ => x a) := HasCirc.proj (fun _ => a)
    have hxor := HasCirc.xor2 ih ha
    refine hxor.weaken (by simp; omega) |>.congr ?_
    intro x _
    simp [List.foldl_append]

def bitsToNat {B : ℕ} (v : Fin B → Bool) : ℕ :=
  ∑ i : Fin B, (v i).toNat * 2 ^ i.val

def natToBits (B x : ℕ) : Fin B → Bool :=
  fun i => x.testBit i.val

lemma bitsToNat_zero (v : Fin 0 → Bool) : bitsToNat v = 0 := by
  simp [bitsToNat]

lemma bitsToNat_succ {B : ℕ} (v : Fin (B + 1) → Bool) :
    bitsToNat v = (v 0).toNat + 2 * bitsToNat (fun i : Fin B => v i.succ) := by
  unfold bitsToNat
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma bitsToNat_castSucc {B : ℕ} (v : Fin (B + 1) → Bool) :
    bitsToNat v = bitsToNat (fun i : Fin B => v i.castSucc) + (v (Fin.last B)).toNat * 2 ^ B := by
  unfold bitsToNat
  rw [Fin.sum_univ_castSucc]
  simp

lemma bitsToNat_lt {B : ℕ} (v : Fin B → Bool) : bitsToNat v < 2 ^ B := by
  induction B with
  | zero => simp [bitsToNat]
  | succ B ih =>
    rw [bitsToNat_succ, pow_succ]
    have h1 := ih (fun i => v i.succ)
    cases v 0 <;> simp <;> omega

lemma bitsToNat_natToBits {B x : ℕ} (hx : x < 2 ^ B) :
    bitsToNat (natToBits B x) = x := by
  induction B generalizing x with
  | zero =>
    simp only [pow_zero] at hx
    have hx0 : x = 0 := by omega
    subst hx0
    simp [bitsToNat]
  | succ B ih =>
    rw [bitsToNat_succ]
    have hdiv : x / 2 < 2 ^ B := by rw [pow_succ] at hx; omega
    have hsucc : (fun i : Fin B => natToBits (B + 1) x i.succ) = natToBits B (x / 2) := by
      funext i
      simp [natToBits, Nat.testBit_succ]
    rw [hsucc, ih hdiv]
    simp only [natToBits, Fin.val_zero, Nat.testBit_zero]
    have hmod := Nat.div_add_mod x 2
    by_cases hodd : x % 2 = 1
    · simp [hodd]; omega
    · have h0 : x % 2 = 0 := by omega
      simp [h0]; omega

lemma natToBits_bitsToNat {B : ℕ} (v : Fin B → Bool) :
    natToBits B (bitsToNat v) = v := by
  induction B with
  | zero => funext i; exact Fin.elim0 i
  | succ B ih =>
    funext i
    refine Fin.cases ?_ ?_ i
    · simp only [natToBits, Fin.val_zero, Nat.testBit_zero, bitsToNat_succ]
      cases v 0 <;> simp
    · intro j
      simp only [natToBits, Fin.val_succ, Nat.testBit_succ, bitsToNat_succ]
      have hdiv : ((v 0).toNat + 2 * bitsToNat (fun k : Fin B => v k.succ)) / 2 =
          bitsToNat (fun k : Fin B => v k.succ) := by
        cases v 0
        · simp
        · simp only [Bool.toNat_true]; omega
      rw [hdiv]
      exact congrFun (ih (fun k => v k.succ)) j

lemma bitsToNat_not {B : ℕ} (v : Fin B → Bool) :
    bitsToNat (fun i => !(v i)) + bitsToNat v + 1 = 2 ^ B := by
  induction B with
  | zero => simp [bitsToNat]
  | succ B ih =>
    rw [bitsToNat_succ, bitsToNat_succ, pow_succ]
    have h1 := ih (fun i => v i.succ)
    cases v 0 <;> simp <;> omega

lemma bitsToNat_inj {B : ℕ} {u v : Fin B → Bool} (h : bitsToNat u = bitsToNat v) : u = v := by
  rw [← natToBits_bitsToNat u, ← natToBits_bitsToNat v, h]

def fullAddFun (x : Fin 3 → Bool) : Fin 2 → Bool
  | ⟨0, _⟩ => Bool.xor (Bool.xor (x 0) (x 1)) (x 2)
  | ⟨1, _⟩ => (x 0 && x 1) || (x 2 && Bool.xor (x 0) (x 1))

lemma fullAdd_spec (a b c : Bool) :
    (Bool.xor (Bool.xor a b) c).toNat + 2 * ((a && b) || (c && Bool.xor a b)).toNat =
      a.toNat + b.toNat + c.toNat := by
  cases a <;> cases b <;> cases c <;> decide

lemma HasCirc.fullAdd : HasCirc 3 2 16 fullAddFun := by
  have ha : HasCirc 3 1 0 (fun x _ => x 0) := HasCirc.proj (fun _ => 0)
  have hb : HasCirc 3 1 0 (fun x _ => x 1) := HasCirc.proj (fun _ => 1)
  have hc : HasCirc 3 1 0 (fun x _ => x 2) := HasCirc.proj (fun _ => 2)
  have hab := HasCirc.xor2 ha hb
  have hsum := HasCirc.xor2 hab hc
  have hcout := HasCirc.or2 (HasCirc.and2 ha hb) (HasCirc.and2 hc (HasCirc.xor2 ha hb))
  refine (HasCirc.pair hsum hcout).weaken (by omega) |>.congr ?_
  intro x j
  fin_cases j
  · exact append_fin1_0
  · exact append_fin1_1

def addCarryFun (B : ℕ) (x : Fin (1 + B + B) → Bool) : Fin (B + 1) → Bool :=
  natToBits (B + 1)
    ((x ⟨0, by omega⟩).toNat +
      bitsToNat (fun i : Fin B => x ⟨1 + i.val, by omega⟩) +
      bitsToNat (fun i : Fin B => x ⟨1 + B + i.val, by omega⟩))

lemma addCarryFun_val (B : ℕ) (x : Fin (1 + B + B) → Bool) :
    bitsToNat (addCarryFun B x) =
      (x ⟨0, by omega⟩).toNat +
      bitsToNat (fun i : Fin B => x ⟨1 + i.val, by omega⟩) +
      bitsToNat (fun i : Fin B => x ⟨1 + B + i.val, by omega⟩) := by
  apply bitsToNat_natToBits
  have ha := bitsToNat_lt (fun i : Fin B => x ⟨1 + i.val, by omega⟩)
  have hb := bitsToNat_lt (fun i : Fin B => x ⟨1 + B + i.val, by omega⟩)
  have hc : (x ⟨0, by omega⟩).toNat ≤ 1 := by cases x ⟨0, by omega⟩ <;> decide
  rw [pow_succ]
  omega

lemma HasCirc.addCarry (B : ℕ) : HasCirc (1 + B + B) (B + 1) (16 * B) (addCarryFun B) := by
  induction B with
  | zero =>
    refine (HasCirc.proj (n := 1) (m := 1) (fun _ => 0)).weaken (by omega) |>.congr ?_
    intro x j
    fin_cases j
    simp [addCarryFun, bitsToNat, natToBits]
    cases x 0 <;> rfl
  | succ B ih =>
    let faIn : Fin 3 → Fin (1 + (B + 1) + (B + 1))
      | ⟨0, _⟩ => ⟨1, by omega⟩
      | ⟨1, _⟩ => ⟨1 + (B + 1), by omega⟩
      | ⟨2, _⟩ => ⟨0, by omega⟩
    have hfa := HasCirc.comp (HasCirc.proj faIn) HasCirc.fullAdd
    let restIn : Fin (B + B) → Fin (1 + (B + 1) + (B + 1)) := fun i =>
      if h : i.val < B then ⟨1 + (i.val + 1), by omega⟩
      else ⟨1 + (B + 1) + (i.val - B + 1), by omega⟩
    have hstage1 := HasCirc.pair hfa (HasCirc.proj restIn)
    let recIn : Fin (1 + B + B) → Fin (2 + (B + B)) := fun i =>
      if h0 : i.val = 0 then ⟨1, by omega⟩
      else ⟨2 + (i.val - 1), by omega⟩
    have hrec := HasCirc.comp (HasCirc.proj recIn) ih
    have hs0 : HasCirc (2 + (B + B)) 1 0 (fun y _ => y ⟨0, by omega⟩) :=
      HasCirc.proj (fun _ => ⟨0, by omega⟩)
    have hstage2 := HasCirc.pair hs0 hrec
    have hall := HasCirc.comp hstage1 hstage2
    have hcast : HasCirc (1 + (B + 1)) (B + 1 + 1) 0 (fun y j => y ⟨j.val, by omega⟩) :=
      HasCirc.proj _
    refine (HasCirc.comp hall hcast).weaken (by omega) |>.congr ?_
    intro x j
    apply congrFun (f := fun j : Fin (B + 1 + 1) => _) (g := addCarryFun (B + 1) x) ?_ j
    apply bitsToNat_inj
    rw [addCarryFun_val]
    set s1 : Fin (2 + (B + B)) → Bool :=
      Fin.append (fullAddFun (fun t => x (faIn t))) (fun r => x (restIn r))
    have htop : bitsToNat (fun j : Fin (B + 1 + 1) =>
        Fin.append (fun _ : Fin 1 => s1 ⟨0, by omega⟩)
          (addCarryFun B (fun i => s1 (recIn i)))
          ⟨j.val, by omega⟩) =
        (s1 ⟨0, by omega⟩).toNat + 2 * bitsToNat (addCarryFun B (fun i => s1 (recIn i))) := by
      rw [bitsToNat_succ]
      have h0 : Fin.append (fun _ : Fin 1 => s1 ⟨0, by omega⟩)
          (addCarryFun B (fun i => s1 (recIn i))) (⟨0, by omega⟩ : Fin (1 + (B + 1))) =
          s1 ⟨0, by omega⟩ := by
        change Fin.append _ _ (Fin.castAdd (B + 1) 0) = _
        rw [Fin.append_left]
      have h1 : (fun i : Fin (B + 1) =>
          Fin.append (fun _ : Fin 1 => s1 ⟨0, by omega⟩)
            (addCarryFun B (fun i => s1 (recIn i))) ⟨i.succ.val, by omega⟩) =
          addCarryFun B (fun i => s1 (recIn i)) := by
        funext i
        have hnat : (⟨i.succ.val, by omega⟩ : Fin (1 + (B + 1))) = Fin.natAdd 1 i := by
          apply Fin.ext; simp [Fin.natAdd]; omega
        rw [hnat, Fin.append_right]
      simp only [Fin.val_zero, h0, h1]
    have hs1_0 : s1 ⟨0, by omega⟩ = fullAddFun (fun t => x (faIn t)) 0 := by
      dsimp [s1]
      change Fin.append _ _ (Fin.castAdd (B + B) 0) = _
      rw [Fin.append_left]
    change bitsToNat (fun j : Fin (B + 1 + 1) =>
        Fin.append (fun _ : Fin 1 => s1 ⟨0, by omega⟩)
          (addCarryFun B (fun i => s1 (recIn i))) ⟨j.val, by omega⟩) = _
    rw [htop, hs1_0, addCarryFun_val]
    have hc1 : s1 (recIn ⟨0, by omega⟩) = fullAddFun (fun t => x (faIn t)) 1 := by
      dsimp [s1, recIn]
      change Fin.append _ _ (Fin.castAdd (B + B) 1) = _
      rw [Fin.append_left]
    have ha' : (fun i : Fin B => s1 (recIn ⟨1 + i.val, by omega⟩)) =
        (fun i : Fin B => x ⟨1 + (i.val + 1), by omega⟩) := by
      funext i
      have hne : ¬ (1 + i.val = 0) := by omega
      dsimp [s1, recIn]
      simp only [hne, ↓reduceDIte]
      have hnat : (⟨2 + (1 + i.val - 1), by omega⟩ : Fin (2 + (B + B))) =
          Fin.natAdd 2 ⟨i.val, by omega⟩ := by apply Fin.ext; simp [Fin.natAdd]
      rw [hnat, Fin.append_right]
      simp [restIn, i.isLt]
    have hb' : (fun i : Fin B => s1 (recIn ⟨1 + B + i.val, by omega⟩)) =
        (fun i : Fin B => x ⟨1 + (B + 1) + (i.val + 1), by omega⟩) := by
      funext i
      have hne : ¬ (1 + B + i.val = 0) := by omega
      dsimp [s1, recIn]
      simp only [hne, ↓reduceDIte]
      have hnat : (⟨2 + (1 + B + i.val - 1), by omega⟩ : Fin (2 + (B + B))) =
          Fin.natAdd 2 ⟨B + i.val, by omega⟩ := by apply Fin.ext; simp [Fin.natAdd]; omega
      rw [hnat, Fin.append_right]
      have hge : ¬ (B + i.val < B) := by omega
      simp only [restIn, hge, ↓reduceDIte]
      congr 1; apply Fin.ext; simp
    rw [hc1, ha', hb']
    have hsa := bitsToNat_succ (fun i : Fin (B + 1) => x ⟨1 + i.val, by omega⟩)
    have hsb := bitsToNat_succ (fun i : Fin (B + 1) => x ⟨1 + (B + 1) + i.val, by omega⟩)
    simp only [Fin.val_zero, Fin.val_succ, Nat.add_zero] at hsa hsb
    rw [hsa, hsb]
    have hfa_eq := fullAdd_spec (x ⟨1, by omega⟩) (x ⟨1 + (B + 1), by omega⟩) (x ⟨0, by omega⟩)
    simp only [fullAddFun, faIn] at hfa_eq ⊢
    omega

def addBFun (B : ℕ) (x : Fin (B + B) → Bool) : Fin (B + 1) → Bool :=
  natToBits (B + 1)
    (bitsToNat (fun i : Fin B => x ⟨i.val, by omega⟩) +
      bitsToNat (fun i : Fin B => x ⟨B + i.val, by omega⟩))

lemma HasCirc.addB (B : ℕ) (hB : 0 < B) :
    HasCirc (B + B) (B + 1) (16 * B + 2) (addBFun B) := by
  have hc0 : HasCirc (B + B) 1 2 (fun _ _ => false) := HasCirc.const (by omega) false
  have hid : HasCirc (B + B) (B + B) 0 (fun x => x) := HasCirc.proj id
  have hp := HasCirc.pair hc0 hid
  have hcast : HasCirc (1 + (B + B)) (1 + B + B) 0 (fun y j => y ⟨j.val, by omega⟩) :=
    HasCirc.proj _
  refine (HasCirc.comp (HasCirc.comp hp hcast) (HasCirc.addCarry B)).weaken (by omega) |>.congr ?_
  intro x j
  unfold addCarryFun addBFun
  dsimp only
  congr 1
  have h0 : Fin.append (fun _ : Fin 1 => false) x ⟨0, by omega⟩ = false := by
    change Fin.append _ _ (Fin.castAdd (B + B) 0) = false
    rw [Fin.append_left]
  have ha : (fun i : Fin B => Fin.append (fun _ : Fin 1 => false) x ⟨1 + i.val, by omega⟩) =
      fun i : Fin B => x ⟨i.val, by omega⟩ := by
    funext i
    have : (⟨1 + i.val, by omega⟩ : Fin (1 + (B + B))) = Fin.natAdd 1 ⟨i.val, by omega⟩ := by
      apply Fin.ext; simp [Fin.natAdd]
    rw [this, Fin.append_right]
  have hb : (fun i : Fin B => Fin.append (fun _ : Fin 1 => false) x ⟨1 + B + i.val, by omega⟩) =
      fun i : Fin B => x ⟨B + i.val, by omega⟩ := by
    funext i
    have : (⟨1 + B + i.val, by omega⟩ : Fin (1 + (B + B))) = Fin.natAdd 1 ⟨B + i.val, by omega⟩ := by
      apply Fin.ext; simp [Fin.natAdd]; omega
    rw [this, Fin.append_right]
  rw [h0, ha, hb]
  simp

def subCmpFun (B : ℕ) (x : Fin (B + B) → Bool) : Fin (B + 1) → Bool :=
  let a := bitsToNat (fun i : Fin B => x ⟨i.val, by omega⟩)
  let b := bitsToNat (fun i : Fin B => x ⟨B + i.val, by omega⟩)
  natToBits (B + 1) (1 + a + (2 ^ B - 1 - b))

lemma subCmpFun_top (B : ℕ) (x : Fin (B + B) → Bool) :
    subCmpFun B x (Fin.last B) =
      decide (bitsToNat (fun i : Fin B => x ⟨B + i.val, by omega⟩) ≤
        bitsToNat (fun i : Fin B => x ⟨i.val, by omega⟩)) := by
  set a := bitsToNat (fun i : Fin B => x ⟨i.val, by omega⟩)
  set b := bitsToNat (fun i : Fin B => x ⟨B + i.val, by omega⟩)
  have ha : a < 2 ^ B := bitsToNat_lt _
  have hb : b < 2 ^ B := bitsToNat_lt _
  have h1 : 1 ≤ 2 ^ B := Nat.one_le_two_pow
  set S := 1 + a + (2 ^ B - 1 - b)
  have hS : S < 2 ^ (B + 1) := by rw [pow_succ]; omega
  have hbit := bitsToNat_castSucc (natToBits (B + 1) S)
  rw [bitsToNat_natToBits hS] at hbit
  have hlow := bitsToNat_lt (fun i : Fin B => natToBits (B + 1) S i.castSucc)
  change (natToBits (B + 1) S (Fin.last B)) = decide (b ≤ a)
  cases hval : natToBits (B + 1) S (Fin.last B)
  · rw [hval] at hbit; simp at hbit
    have hlt : S < 2 ^ B := by omega
    have hnot : ¬ (b ≤ a) := by omega
    simp [hnot]
  · rw [hval] at hbit; simp at hbit
    have hge : 2 ^ B ≤ S := by omega
    have hle : b ≤ a := by omega
    simp [hle]

lemma subCmpFun_low {B : ℕ} (x : Fin (B + B) → Bool)
    (hle : bitsToNat (fun i : Fin B => x ⟨B + i.val, by omega⟩) ≤
      bitsToNat (fun i : Fin B => x ⟨i.val, by omega⟩)) :
    bitsToNat (fun i : Fin B => subCmpFun B x i.castSucc) =
      bitsToNat (fun i : Fin B => x ⟨i.val, by omega⟩) -
      bitsToNat (fun i : Fin B => x ⟨B + i.val, by omega⟩) := by
  set a := bitsToNat (fun i : Fin B => x ⟨i.val, by omega⟩)
  set b := bitsToNat (fun i : Fin B => x ⟨B + i.val, by omega⟩)
  have ha : a < 2 ^ B := bitsToNat_lt _
  have hb : b < 2 ^ B := bitsToNat_lt _
  have h1 : 1 ≤ 2 ^ B := Nat.one_le_two_pow
  set S := 1 + a + (2 ^ B - 1 - b)
  have hS : S < 2 ^ (B + 1) := by rw [pow_succ]; omega
  have htop : subCmpFun B x (Fin.last B) = true := by
    rw [subCmpFun_top]
    exact decide_eq_true hle
  have hbit := bitsToNat_castSucc (subCmpFun B x)
  have htot : bitsToNat (subCmpFun B x) = S := bitsToNat_natToBits hS
  rw [htot, htop] at hbit
  simp at hbit
  omega

lemma HasCirc.subCmp (B : ℕ) (hB : 0 < B) :
    HasCirc (B + B) (B + 1) (17 * B + 2) (subCmpFun B) := by
  have hc1 : HasCirc (B + B) 1 2 (fun _ _ => true) := HasCirc.const (by omega) true
  have ha : HasCirc (B + B) B 0 (fun x i => x ⟨i.val, by omega⟩) := HasCirc.proj _
  have hnb : HasCirc (B + B) B (B * 1) (fun x i => !(x ⟨B + i.val, by omega⟩)) :=
    HasCirc.vecConst (B := 1) (fun i =>
      (HasCirc.not1 (HasCirc.proj (n := B + B) (m := 1) (fun _ => ⟨B + i.val, by omega⟩))).weaken (by omega))
  have hp := HasCirc.pair (HasCirc.pair hc1 ha) hnb
  have hcomp := HasCirc.comp hp (HasCirc.addCarry B)
  refine hcomp.weaken (by omega) |>.congr ?_
  intro x j
  unfold addCarryFun subCmpFun
  congr 1
  have h0 : Fin.append (Fin.append (fun _ : Fin 1 => true) (fun i : Fin B => x ⟨i.val, by omega⟩))
      (fun i : Fin B => !(x ⟨B + i.val, by omega⟩)) ⟨0, by omega⟩ = true := by
    change Fin.append _ _ (Fin.castAdd B (Fin.castAdd B 0)) = true
    rw [Fin.append_left, Fin.append_left]
  have ha' : (fun i : Fin B =>
      Fin.append (Fin.append (fun _ : Fin 1 => true) (fun i : Fin B => x ⟨i.val, by omega⟩))
        (fun i : Fin B => !(x ⟨B + i.val, by omega⟩)) ⟨1 + i.val, by omega⟩) =
      fun i : Fin B => x ⟨i.val, by omega⟩ := by
    funext i
    have : (⟨1 + i.val, by omega⟩ : Fin (1 + B + B)) = Fin.castAdd B (Fin.natAdd 1 i) := by
      apply Fin.ext; simp [Fin.natAdd]
    rw [this, Fin.append_left, Fin.append_right]
  have hb' : (fun i : Fin B =>
      Fin.append (Fin.append (fun _ : Fin 1 => true) (fun i : Fin B => x ⟨i.val, by omega⟩))
        (fun i : Fin B => !(x ⟨B + i.val, by omega⟩)) ⟨1 + B + i.val, by omega⟩) =
      fun i : Fin B => !(x ⟨B + i.val, by omega⟩) := by
    funext i
    have : (⟨1 + B + i.val, by omega⟩ : Fin (1 + B + B)) = Fin.natAdd (1 + B) i := by
      apply Fin.ext; simp [Fin.natAdd]
    rw [this, Fin.append_right]
  rw [h0, ha', hb']
  have hnot := bitsToNat_not (fun i : Fin B => x ⟨B + i.val, by omega⟩)
  have hlt := bitsToNat_lt (fun i : Fin B => x ⟨B + i.val, by omega⟩)
  have h1 : 1 ≤ 2 ^ B := Nat.one_le_two_pow
  simp only [Bool.toNat_true]
  omega

def popcountVal {m : ℕ} (x : Fin m → Bool) : ℕ :=
  ∑ i : Fin m, (x i).toNat

lemma popcountVal_eq_card {m : ℕ} (x : Fin m → Bool) :
    popcountVal x = (Finset.univ.filter (fun i : Fin m => x i = true)).card := by
  unfold popcountVal
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro i _
  cases x i <;> simp

lemma popcountVal_le {m : ℕ} (x : Fin m → Bool) : popcountVal x ≤ m := by
  rw [popcountVal_eq_card]
  exact (Finset.card_le_univ _).trans (by simp)

lemma HasCirc.popcountTree (m : ℕ) :
    HasCirc (2 ^ m) (m + 1) (36 * 2 ^ m - 18 * (m + 2))
      (fun x => natToBits (m + 1) (popcountVal x)) := by
  induction m with
  | zero =>
    refine (HasCirc.proj (n := 1) (m := 1) (fun _ => 0)).weaken (by omega) |>.congr ?_
    intro x j
    fin_cases j
    simp [popcountVal, natToBits]
    cases x 0 <;> rfl
  | succ m ih =>
    have hhalf : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := by rw [pow_succ]; omega
    let leftIn : Fin (2 ^ m) → Fin (2 ^ (m + 1)) := fun i => ⟨i.val, by omega⟩
    let rightIn : Fin (2 ^ m) → Fin (2 ^ (m + 1)) := fun i => ⟨2 ^ m + i.val, by omega⟩
    have hL := HasCirc.comp (HasCirc.proj leftIn) ih
    have hR := HasCirc.comp (HasCirc.proj rightIn) ih
    have hp := HasCirc.pair hL hR
    have hadd := HasCirc.addB (m + 1) (by omega)
    have hcomp := HasCirc.comp hp hadd
    have hbd : (0 + (36 * 2 ^ m - 18 * (m + 2)) + (0 + (36 * 2 ^ m - 18 * (m + 2)))) +
        (16 * (m + 1) + 2) ≤ 36 * 2 ^ (m + 1) - 18 * (m + 1 + 2) := by
      have hge : 18 * (m + 2) ≤ 36 * 2 ^ m := by
        have : m + 2 ≤ 2 * 2 ^ m := by
          clear ih hL hR hp hadd hcomp
          induction m with
          | zero => omega
          | succ k ihk => rw [pow_succ]; omega
        omega
      rw [pow_succ]
      omega
    refine hcomp.weaken hbd |>.congr ?_
    intro x j
    unfold addBFun
    congr 1
    have hLv : bitsToNat (fun i : Fin (m + 1) =>
        Fin.append (natToBits (m + 1) (popcountVal fun a => x (leftIn a)))
          (natToBits (m + 1) (popcountVal fun a => x (rightIn a))) ⟨i.val, by omega⟩) =
        popcountVal (fun a => x (leftIn a)) := by
      have heq : (fun i : Fin (m + 1) =>
          Fin.append (natToBits (m + 1) (popcountVal fun a => x (leftIn a)))
            (natToBits (m + 1) (popcountVal fun a => x (rightIn a))) ⟨i.val, by omega⟩) =
          natToBits (m + 1) (popcountVal fun a => x (leftIn a)) := by
        funext i
        change Fin.append _ _ (Fin.castAdd (m + 1) i) = _
        rw [Fin.append_left]
      rw [heq]
      apply bitsToNat_natToBits
      have hle := popcountVal_le (fun a => x (leftIn a))
      rw [pow_succ]; omega
    have hRv : bitsToNat (fun i : Fin (m + 1) =>
        Fin.append (natToBits (m + 1) (popcountVal fun a => x (leftIn a)))
          (natToBits (m + 1) (popcountVal fun a => x (rightIn a))) ⟨m + 1 + i.val, by omega⟩) =
        popcountVal (fun a => x (rightIn a)) := by
      have heq : (fun i : Fin (m + 1) =>
          Fin.append (natToBits (m + 1) (popcountVal fun a => x (leftIn a)))
            (natToBits (m + 1) (popcountVal fun a => x (rightIn a))) ⟨m + 1 + i.val, by omega⟩) =
          natToBits (m + 1) (popcountVal fun a => x (rightIn a)) := by
        funext i
        have : (⟨m + 1 + i.val, by omega⟩ : Fin (m + 1 + (m + 1))) = Fin.natAdd (m + 1) i := by
          apply Fin.ext; simp [Fin.natAdd]
        rw [this, Fin.append_right]
      rw [heq]
      apply bitsToNat_natToBits
      have hle := popcountVal_le (fun a => x (rightIn a))
      rw [pow_succ]; omega
    rw [hLv, hRv]
    unfold popcountVal
    symm
    calc ∑ i : Fin (2 ^ (m + 1)), (x i).toNat
        = ∑ i : Fin (2 ^ m + 2 ^ m), (x ⟨i.val, by omega⟩).toNat :=
          Fintype.sum_equiv (finCongr hhalf) _ _ (fun _ => rfl)
      _ = ∑ i : Fin (2 ^ m), (x (leftIn i)).toNat + ∑ i : Fin (2 ^ m), (x (rightIn i)).toNat :=
          Fin.sum_univ_add (f := fun i : Fin (2 ^ m + 2 ^ m) => (x ⟨i.val, by omega⟩).toNat)

lemma band_iff_interval (n d : ℕ) :
    (16 * Nat.dist (2 * d) n ≤ n) ↔ ((15 * n + 31) / 32 ≤ d ∧ d ≤ (17 * n) / 32) := by
  have hd : Nat.dist (2 * d) n = if 2 * d ≤ n then n - 2 * d else 2 * d - n := by
    unfold Nat.dist
    split_ifs <;> omega
  rw [hd]
  split_ifs <;> omega

lemma HasCirc.constBits {n B : ℕ} (hn : 0 < n) (val : ℕ) :
    HasCirc n B (2 * B) (fun _ => natToBits B val) := by
  have h := HasCirc.vecConst (n := n) (m := B) (B := 2) (f := fun _ => natToBits B val)
    (fun j => HasCirc.const hn (val.testBit j.val))
  simpa [Nat.mul_comm] using h

lemma HasCirc.flagCirc (k : ℕ) (hk : 4 ≤ k) :
    let n := k - 1
    HasCirc (k + n) 1 (200 * (k + 1)) (fun x _ =>
      let d := popcountVal (fun j : Fin n => Bool.xor (x ⟨j.val, by omega⟩) (x ⟨k + j.val, by omega⟩))
      decide (16 * Nat.dist (2 * d) n ≤ n)) := by
  intro n
  have hn : 1 ≤ n := by omega
  set m := Nat.log 2 n + 1
  have hle2m : n ≤ 2 ^ m := le_of_lt (Nat.lt_pow_succ_log_self (by omega) n)
  have h2mlt : 2 ^ m ≤ 2 * n := by
    have hlog : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 (by omega)
    have hpow : 2 ^ m = 2 * 2 ^ Nat.log 2 n := by rw [show m = Nat.log 2 n + 1 from rfl, pow_succ]; ring
    omega
  have hm_le : m ≤ n := by
    have : Nat.log 2 n < 2 ^ Nat.log 2 n := Nat.lt_two_pow_self
    have hlog : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 (by omega)
    omega
  have hxor : HasCirc (k + n) n (4 * n)
      (fun x j => Bool.xor (x ⟨j.val, by omega⟩) (x ⟨k + j.val, by omega⟩)) := by
    have h := HasCirc.vecConst (n := k + n) (m := n) (B := 4)
      (fun j => HasCirc.xor2
        (HasCirc.proj (n := k + n) (m := 1) (fun _ => ⟨j.val, by omega⟩))
        (HasCirc.proj (n := k + n) (m := 1) (fun _ => ⟨k + j.val, by omega⟩)))
    simpa [Nat.mul_comm] using h
  have hc0 : HasCirc (k + n) 1 2 (fun _ _ => false) := HasCirc.const (by omega) false
  have hpad : HasCirc (k + n) (2 ^ m) (4 * n + 2)
      (fun x i => if h : i.val < n then Bool.xor (x ⟨i.val, by omega⟩) (x ⟨k + i.val, by omega⟩) else false) := by
    let idx : Fin (2 ^ m) → Fin (n + 1) := fun i =>
      if h : i.val < n then ⟨i.val, by omega⟩ else ⟨n, by omega⟩
    refine (HasCirc.comp (HasCirc.pair hxor hc0) (HasCirc.proj idx)).weaken (by omega) |>.congr ?_
    intro x i
    dsimp [idx]
    split_ifs with hi
    · change Fin.append _ _ (Fin.castAdd 1 ⟨i.val, hi⟩) = _
      rw [Fin.append_left]
    · change Fin.append _ _ (Fin.natAdd n 0) = _
      rw [Fin.append_right]
  have hpop := HasCirc.comp hpad (HasCirc.popcountTree m)
  set lo := (15 * n + 31) / 32
  set hi := (17 * n) / 32
  have hlo_lt : lo < 2 ^ (m + 1) := by rw [pow_succ]; omega
  have hhi_lt : hi < 2 ^ (m + 1) := by rw [pow_succ]; omega
  have hconstLo : HasCirc (m + 1) (m + 1) (2 * (m + 1)) (fun _ => natToBits (m + 1) lo) :=
    HasCirc.constBits (by omega) lo
  have hconstHi : HasCirc (m + 1) (m + 1) (2 * (m + 1)) (fun _ => natToBits (m + 1) hi) :=
    HasCirc.constBits (by omega) hi
  have hid : HasCirc (m + 1) (m + 1) 0 (fun y => y) := HasCirc.proj id
  have hgeLo : HasCirc (m + 1) 1 (2 * (m + 1) + (17 * (m + 1) + 2))
      (fun y _ => decide (lo ≤ bitsToNat y)) := by
    have h1 := HasCirc.comp (HasCirc.pair hid hconstLo) (HasCirc.subCmp (m + 1) (by omega))
    have h2 := HasCirc.comp h1 (HasCirc.proj (fun _ : Fin 1 => Fin.last (m + 1)))
    refine h2.weaken (by omega) |>.congr ?_
    intro y _
    rw [subCmpFun_top]
    have hL : (fun i : Fin (m + 1) => Fin.append y (natToBits (m + 1) lo) ⟨i.val, by omega⟩) = y := by
      funext i
      change Fin.append _ _ (Fin.castAdd (m + 1) i) = _
      rw [Fin.append_left]
    have hR : (fun i : Fin (m + 1) => Fin.append y (natToBits (m + 1) lo) ⟨m + 1 + i.val, by omega⟩) =
        natToBits (m + 1) lo := by
      funext i
      have : (⟨m + 1 + i.val, by omega⟩ : Fin (m + 1 + (m + 1))) = Fin.natAdd (m + 1) i := by
        apply Fin.ext; simp [Fin.natAdd]
      rw [this, Fin.append_right]
    rw [hL, hR, bitsToNat_natToBits hlo_lt]
  have hleHi : HasCirc (m + 1) 1 (2 * (m + 1) + (17 * (m + 1) + 2))
      (fun y _ => decide (bitsToNat y ≤ hi)) := by
    have h1 := HasCirc.comp (HasCirc.pair hconstHi hid) (HasCirc.subCmp (m + 1) (by omega))
    have h2 := HasCirc.comp h1 (HasCirc.proj (fun _ : Fin 1 => Fin.last (m + 1)))
    refine h2.weaken (by omega) |>.congr ?_
    intro y _
    rw [subCmpFun_top]
    have hL : (fun i : Fin (m + 1) => Fin.append (natToBits (m + 1) hi) y ⟨i.val, by omega⟩) =
        natToBits (m + 1) hi := by
      funext i
      change Fin.append _ _ (Fin.castAdd (m + 1) i) = _
      rw [Fin.append_left]
    have hR : (fun i : Fin (m + 1) => Fin.append (natToBits (m + 1) hi) y ⟨m + 1 + i.val, by omega⟩) = y := by
      funext i
      have : (⟨m + 1 + i.val, by omega⟩ : Fin (m + 1 + (m + 1))) = Fin.natAdd (m + 1) i := by
        apply Fin.ext; simp [Fin.natAdd]
      rw [this, Fin.append_right]
    rw [hL, hR, bitsToNat_natToBits hhi_lt]
  have hband := HasCirc.and2 hgeLo hleHi
  have hall := HasCirc.comp hpop hband
  have hbudget :
      (4 * n + 2 + (36 * 2 ^ m - 18 * (m + 2))) +
        (2 * (m + 1) + (17 * (m + 1) + 2) + (2 * (m + 1) + (17 * (m + 1) + 2)) + 1) ≤
      200 * (k + 1) := by
    omega
  refine hall.weaken hbudget |>.congr ?_
  intro x _
  have hpeq : popcountVal (fun i : Fin (2 ^ m) =>
      if h : i.val < n then Bool.xor (x ⟨i.val, by omega⟩) (x ⟨k + i.val, by omega⟩) else false) =
      popcountVal (fun j : Fin n => Bool.xor (x ⟨j.val, by omega⟩) (x ⟨k + j.val, by omega⟩)) := by
    unfold popcountVal
    have hsplit : 2 ^ m = n + (2 ^ m - n) := by omega
    calc ∑ i : Fin (2 ^ m),
          (if h : i.val < n then Bool.xor (x ⟨i.val, by omega⟩) (x ⟨k + i.val, by omega⟩) else false).toNat
        = ∑ i : Fin (n + (2 ^ m - n)),
          (if h : i.val < n then Bool.xor (x ⟨i.val, by omega⟩) (x ⟨k + i.val, by omega⟩) else false).toNat :=
          Fintype.sum_equiv (finCongr hsplit) _ _ (fun _ => rfl)
      _ = ∑ j : Fin n,
          (if h : (Fin.castAdd (2 ^ m - n) j).val < n then
            Bool.xor (x ⟨(Fin.castAdd (2 ^ m - n) j).val, by omega⟩) (x ⟨k + (Fin.castAdd (2 ^ m - n) j).val, by omega⟩)
          else false).toNat +
          ∑ j : Fin (2 ^ m - n),
          (if h : (Fin.natAdd n j).val < n then
            Bool.xor (x ⟨(Fin.natAdd n j).val, by omega⟩) (x ⟨k + (Fin.natAdd n j).val, by omega⟩)
          else false).toNat := Fin.sum_univ_add _
      _ = ∑ j : Fin n, (Bool.xor (x ⟨j.val, by omega⟩) (x ⟨k + j.val, by omega⟩)).toNat + 0 := by
          congr 1
          · apply Finset.sum_congr rfl; intro j _; simp [Fin.castAdd, j.isLt]
          · apply Finset.sum_eq_zero; intro j _
            have : ¬ (n + j.val < n) := by omega
            simp [Fin.natAdd, this]
      _ = ∑ j : Fin n, (Bool.xor (x ⟨j.val, by omega⟩) (x ⟨k + j.val, by omega⟩)).toNat := Nat.add_zero _
  rw [hpeq]
  set d := popcountVal (fun j : Fin n => Bool.xor (x ⟨j.val, by omega⟩) (x ⟨k + j.val, by omega⟩))
  have hd_lt : d < 2 ^ (m + 1) := by
    have := popcountVal_le (fun j : Fin n => Bool.xor (x ⟨j.val, by omega⟩) (x ⟨k + j.val, by omega⟩))
    rw [pow_succ]; omega
  rw [bitsToNat_natToBits hd_lt]
  have hiff := band_iff_interval n d
  by_cases h1 : lo ≤ d ∧ d ≤ hi
  · have h2 : 16 * Nat.dist (2 * d) n ≤ n := hiff.mpr h1
    simp only [h1.1, h1.2, decide_true, Bool.and_self]
    exact (decide_eq_true h2).symm
  · have h2 : ¬ (16 * Nat.dist (2 * d) n ≤ n) := fun h => h1 (hiff.mp h)
    rw [decide_eq_false h2]
    by_cases hlo : lo ≤ d
    · have hhi : ¬ (d ≤ hi) := fun hh => h1 ⟨hlo, hh⟩
      simp [hlo, hhi]
    · simp [hlo]

def tritSum (x z : Bool) : Fin 3 :=
  ⟨x.toNat + z.toNat, by cases x <;> cases z <;> decide⟩

def encode5 (t : Fin 5 → Fin 3) : ℕ :=
  ∑ i : Fin 5, (t i).val * 3 ^ i.val

lemma encode5_eq (t : Fin 5 → Fin 3) :
    encode5 t = (t 0).val + 3 * (t 1).val + 9 * (t 2).val + 27 * (t 3).val + 81 * (t 4).val := by
  simp [encode5, Fin.sum_univ_five]
  ring

lemma encode5_lt (t : Fin 5 → Fin 3) : encode5 t < 256 := by
  rw [encode5_eq]
  have h0 := (t 0).isLt
  have h1 := (t 1).isLt
  have h2 := (t 2).isLt
  have h3 := (t 3).isLt
  have h4 := (t 4).isLt
  omega

lemma encode5_inj {t1 t2 : Fin 5 → Fin 3} (h : encode5 t1 = encode5 t2) : t1 = t2 := by
  rw [encode5_eq, encode5_eq] at h
  have h01 := (t1 0).isLt; have h11 := (t1 1).isLt; have h21 := (t1 2).isLt
  have h31 := (t1 3).isLt; have h41 := (t1 4).isLt
  have h02 := (t2 0).isLt; have h12 := (t2 1).isLt; have h22 := (t2 2).isLt
  have h32 := (t2 3).isLt; have h42 := (t2 4).isLt
  funext i
  fin_cases i <;> apply Fin.ext <;> dsimp <;> omega

def decode5 (code : ℕ) (i : Fin 5) : Fin 3 :=
  ⟨(code / 3 ^ i.val) % 3, Nat.mod_lt _ (by omega)⟩

lemma decode5_encode5 (t : Fin 5 → Fin 3) (i : Fin 5) :
    decode5 (encode5 t) i = t i := by
  have he := encode5_eq t
  have h0 := (t 0).isLt; have h1 := (t 1).isLt; have h2 := (t 2).isLt
  have h3 := (t 3).isLt; have h4 := (t 4).isLt
  fin_cases i <;> apply Fin.ext <;> dsimp [decode5] <;> rw [he] <;> omega

def pack5Bits (inp : Fin 10 → Bool) : Fin 8 → Bool :=
  natToBits 8 (encode5 fun i : Fin 5 => tritSum (inp ⟨i.val, by omega⟩) (inp ⟨5 + i.val, by omega⟩))

def unpack5Bits (code : Fin 8 → Bool) : Fin 10 → Bool := fun j =>
  let t := decode5 (bitsToNat code) ⟨j.val / 2, by omega⟩
  if j.val % 2 = 0 then decide (t.val = 1) else decide (t.val = 2)

def recoverBit (is1 is2 y : Bool) : Bool :=
  is2 || (is1 && !y)

lemma recoverBit_left (x z : Bool) :
    recoverBit (decide ((tritSum x z).val = 1)) (decide ((tritSum x z).val = 2)) z = x := by
  cases x <;> cases z <;> rfl

lemma recoverBit_right (x z : Bool) :
    recoverBit (decide ((tritSum x z).val = 1)) (decide ((tritSum x z).val = 2)) x = z := by
  cases x <;> cases z <;> rfl

lemma unpack5_pack5 (inp : Fin 10 → Bool) (i : Fin 5) :
    unpack5Bits (pack5Bits inp) ⟨2 * i.val, by omega⟩ =
      decide ((tritSum (inp ⟨i.val, by omega⟩) (inp ⟨5 + i.val, by omega⟩)).val = 1) ∧
    unpack5Bits (pack5Bits inp) ⟨2 * i.val + 1, by omega⟩ =
      decide ((tritSum (inp ⟨i.val, by omega⟩) (inp ⟨5 + i.val, by omega⟩)).val = 2) := by
  have hlt : encode5 (fun j : Fin 5 => tritSum (inp ⟨j.val, by omega⟩) (inp ⟨5 + j.val, by omega⟩)) < 2 ^ 8 :=
    encode5_lt _
  unfold unpack5Bits pack5Bits
  rw [bitsToNat_natToBits hlt]
  constructor
  · have hdiv : (2 * i.val) / 2 = i.val := by omega
    have hmod : (2 * i.val) % 2 = 0 := by omega
    simp only [hmod, ↓reduceIte]
    have hidx : (⟨(2 * i.val) / 2, by omega⟩ : Fin 5) = i := Fin.ext hdiv
    rw [hidx, decode5_encode5]
  · have hdiv : (2 * i.val + 1) / 2 = i.val := by omega
    have hmod : ¬ ((2 * i.val + 1) % 2 = 0) := by omega
    simp only [hmod, ↓reduceIte]
    have hidx : (⟨(2 * i.val + 1) / 2, by omega⟩ : Fin 5) = i := Fin.ext hdiv
    rw [hidx, decode5_encode5]

def packAllTrits (n : ℕ) (x z : Fin n → Bool) : Fin (((n + 4) / 5) * 8) → Bool := fun j =>
  let b := j.val / 8
  let bit := j.val % 8
  let inp : Fin 10 → Bool := fun t =>
    if h : t.val < 5 then
      if h2 : 5 * b + t.val < n then x ⟨5 * b + t.val, h2⟩ else false
    else
      if h2 : 5 * b + (t.val - 5) < n then z ⟨5 * b + (t.val - 5), h2⟩ else false
  pack5Bits inp ⟨bit, Nat.mod_lt _ (by omega)⟩

lemma packAllTrits_eq_imp {n : ℕ} {x1 z1 x2 z2 : Fin n → Bool}
    (h : packAllTrits n x1 z1 = packAllTrits n x2 z2) (j : Fin n) :
    (x1 j).toNat + (z1 j).toNat = (x2 j).toNat + (z2 j).toNat := by
  set b := j.val / 5
  set r := j.val % 5
  have hq : b < (n + 4) / 5 := by omega
  have hr : r < 5 := by omega
  have hj : 5 * b + r = j.val := by omega
  let inp1 : Fin 10 → Bool := fun t =>
    if h : t.val < 5 then
      if h2 : 5 * b + t.val < n then x1 ⟨5 * b + t.val, h2⟩ else false
    else
      if h2 : 5 * b + (t.val - 5) < n then z1 ⟨5 * b + (t.val - 5), h2⟩ else false
  let inp2 : Fin 10 → Bool := fun t =>
    if h : t.val < 5 then
      if h2 : 5 * b + t.val < n then x2 ⟨5 * b + t.val, h2⟩ else false
    else
      if h2 : 5 * b + (t.val - 5) < n then z2 ⟨5 * b + (t.val - 5), h2⟩ else false
  have hp5 : pack5Bits inp1 = pack5Bits inp2 := by
    funext bit
    have hidx : b * 8 + bit.val < ((n + 4) / 5) * 8 := by omega
    have hEq := congrFun h ⟨b * 8 + bit.val, hidx⟩
    have hd : (b * 8 + bit.val) / 8 = b := by omega
    have hm : (b * 8 + bit.val) % 8 = bit.val := by omega
    simpa [packAllTrits, hd, hm, inp1, inp2] using hEq
  have henc : encode5 (fun i : Fin 5 => tritSum (inp1 ⟨i.val, by omega⟩) (inp1 ⟨5 + i.val, by omega⟩)) =
      encode5 (fun i : Fin 5 => tritSum (inp2 ⟨i.val, by omega⟩) (inp2 ⟨5 + i.val, by omega⟩)) := by
    have h1 := bitsToNat_natToBits (B := 8) (encode5_lt (fun i : Fin 5 => tritSum (inp1 ⟨i.val, by omega⟩) (inp1 ⟨5 + i.val, by omega⟩)))
    have h2 := bitsToNat_natToBits (B := 8) (encode5_lt (fun i : Fin 5 => tritSum (inp2 ⟨i.val, by omega⟩) (inp2 ⟨5 + i.val, by omega⟩)))
    have hb : bitsToNat (pack5Bits inp1) = bitsToNat (pack5Bits inp2) := congrArg bitsToNat hp5
    simpa [pack5Bits, h1, h2] using hb
  have htrit := congrFun (encode5_inj henc) ⟨r, hr⟩
  have hval := congrArg Fin.val htrit
  have hlt : 5 * b + r < n := by omega
  have hr_ge : ¬ (5 + r < 5) := by omega
  simp only [tritSum, inp1, inp2, hr, hr_ge, ↓reduceDIte, hlt, Nat.add_sub_cancel_left] at hval
  have hjeq : (⟨5 * b + r, hlt⟩ : Fin n) = j := Fin.ext hj
  rw [hjeq] at hval
  exact hval

lemma HasCirc.packAllTritsCirc (k : ℕ) (hk : 4 ≤ k) :
    let n := k - 1
    let q := (n + 4) / 5
    HasCirc (k + n) (q * 8) (q * 82000) (fun inp =>
      packAllTrits n (fun j : Fin n => inp ⟨j.val, by omega⟩)
        (fun j : Fin n => inp ⟨k + j.val, by omega⟩)) := by
  intro n q
  have hblk : ∀ b : Fin q,
      HasCirc (k + n) 8 82000 (fun inp =>
        let p : Fin 10 → Bool := fun t =>
          if h : t.val < 5 then
            if h2 : 5 * b.val + t.val < n then inp ⟨5 * b.val + t.val, by omega⟩ else false
          else
            if h2 : 5 * b.val + (t.val - 5) < n then inp ⟨k + (5 * b.val + (t.val - 5)), by omega⟩ else false
        pack5Bits p) := by
    intro b
    have h10 : HasCirc (k + n) 10 (10 * 2) (fun inp t =>
        if h : t.val < 5 then
          if h2 : 5 * b.val + t.val < n then inp ⟨5 * b.val + t.val, by omega⟩ else false
        else
          if h2 : 5 * b.val + (t.val - 5) < n then inp ⟨k + (5 * b.val + (t.val - 5)), by omega⟩ else false) := by
      apply HasCirc.vecConst (B := 2)
      intro t
      split_ifs with h1 h2 h3
      · exact (HasCirc.proj (n := k + n) (m := 1) (fun _ => ⟨5 * b.val + t.val, by omega⟩)).weaken (by omega)
      · exact HasCirc.const (by omega) false
      · exact (HasCirc.proj (n := k + n) (m := 1) (fun _ => ⟨k + (5 * b.val + (t.val - 5)), by omega⟩)).weaken (by omega)
      · exact HasCirc.const (by omega) false
    have hpack : HasCirc 10 8 (8 * (10 * 2 ^ 10)) pack5Bits := HasCirc.table 10 8 (by omega) pack5Bits
    exact (HasCirc.comp h10 hpack).weaken (by norm_num)
  refine (HasCirc.finBlocks (hw := by omega) hblk).congr ?_
  intro inp j
  rfl

def unpackPartner (n : ℕ) (packed : Fin (((n + 4) / 5) * 8) → Bool) (y : Fin n → Bool) : Fin n → Bool :=
  fun j =>
    let b := j.val / 5
    let r := j.val % 5
    let code : Fin 8 → Bool := fun bit => packed ⟨b * 8 + bit.val, by omega⟩
    let u := unpack5Bits code
    recoverBit (u ⟨2 * r, by omega⟩) (u ⟨2 * r + 1, by omega⟩) (y j)

lemma unpackPartner_left {n : ℕ} (x z : Fin n → Bool) :
    unpackPartner n (packAllTrits n x z) z = x := by
  funext j
  unfold unpackPartner
  dsimp only
  set b := j.val / 5
  set r := j.val % 5
  have hr : r < 5 := by omega
  have hj : 5 * b + r = j.val := by omega
  let inp : Fin 10 → Bool := fun t =>
    if h : t.val < 5 then
      if h2 : 5 * b + t.val < n then x ⟨5 * b + t.val, h2⟩ else false
    else
      if h2 : 5 * b + (t.val - 5) < n then z ⟨5 * b + (t.val - 5), h2⟩ else false
  have hcode : (fun bit : Fin 8 => packAllTrits n x z ⟨b * 8 + bit.val, by omega⟩) = pack5Bits inp := by
    funext bit
    have hd : (b * 8 + bit.val) / 8 = b := by omega
    have hm : (b * 8 + bit.val) % 8 = bit.val := by omega
    simp [packAllTrits, hd, hm, inp]
  rw [hcode]
  rcases unpack5_pack5 inp ⟨r, hr⟩ with ⟨h1, h2⟩
  rw [h1, h2]
  have hlt : 5 * b + r < n := by omega
  have hr_ge : ¬ (5 + r < 5) := by omega
  simp only [inp, hr, hr_ge, ↓reduceDIte, hlt, Nat.add_sub_cancel_left]
  have hjeq : (⟨5 * b + r, hlt⟩ : Fin n) = j := Fin.ext hj
  rw [hjeq, recoverBit_left]

lemma unpackPartner_right {n : ℕ} (x z : Fin n → Bool) :
    unpackPartner n (packAllTrits n x z) x = z := by
  funext j
  unfold unpackPartner
  dsimp only
  set b := j.val / 5
  set r := j.val % 5
  have hr : r < 5 := by omega
  have hj : 5 * b + r = j.val := by omega
  let inp : Fin 10 → Bool := fun t =>
    if h : t.val < 5 then
      if h2 : 5 * b + t.val < n then x ⟨5 * b + t.val, h2⟩ else false
    else
      if h2 : 5 * b + (t.val - 5) < n then z ⟨5 * b + (t.val - 5), h2⟩ else false
  have hcode : (fun bit : Fin 8 => packAllTrits n x z ⟨b * 8 + bit.val, by omega⟩) = pack5Bits inp := by
    funext bit
    have hd : (b * 8 + bit.val) / 8 = b := by omega
    have hm : (b * 8 + bit.val) % 8 = bit.val := by omega
    simp [packAllTrits, hd, hm, inp]
  rw [hcode]
  rcases unpack5_pack5 inp ⟨r, hr⟩ with ⟨h1, h2⟩
  rw [h1, h2]
  have hlt : 5 * b + r < n := by omega
  have hr_ge : ¬ (5 + r < 5) := by omega
  simp only [inp, hr, hr_ge, ↓reduceDIte, hlt, Nat.add_sub_cancel_left]
  have hjeq : (⟨5 * b + r, hlt⟩ : Fin n) = j := Fin.ext hj
  rw [hjeq, recoverBit_right]

lemma HasCirc.unpackPartnerCirc (n : ℕ) :
    let q := (n + 4) / 5
    HasCirc (q * 8 + n) n (q * 25600 + 3 * n) (fun inp =>
      unpackPartner n (fun i : Fin (q * 8) => inp ⟨i.val, by omega⟩)
        (fun j : Fin n => inp ⟨q * 8 + j.val, by omega⟩)) := by
  intro q
  have hblk : ∀ b : Fin q,
      HasCirc (q * 8 + n) 10 25600 (fun inp =>
        unpack5Bits (fun bit : Fin 8 => inp ⟨b.val * 8 + bit.val, by omega⟩)) := by
    intro b
    have hproj : HasCirc (q * 8 + n) 8 0 (fun inp bit => inp ⟨b.val * 8 + bit.val, by omega⟩) :=
      HasCirc.proj _
    have hunp : HasCirc 8 10 (10 * (10 * 2 ^ 8)) unpack5Bits :=
      HasCirc.table 8 10 (by omega) unpack5Bits
    exact (HasCirc.comp hproj hunp).weaken (by norm_num)
  have hallUnp := HasCirc.finBlocks (hw := by omega) hblk
  have hy : HasCirc (q * 8 + n) n 0 (fun inp j => inp ⟨q * 8 + j.val, by omega⟩) := HasCirc.proj _
  have hstage1 := HasCirc.pair hallUnp hy
  have hrec : HasCirc (q * 10 + n) n (n * 3) (fun st j =>
      recoverBit (st ⟨(j.val / 5) * 10 + 2 * (j.val % 5), by omega⟩)
        (st ⟨(j.val / 5) * 10 + (2 * (j.val % 5) + 1), by omega⟩)
        (st ⟨q * 10 + j.val, by omega⟩)) := by
    apply HasCirc.vecConst (B := 3)
    intro j
    have hi1 : HasCirc (q * 10 + n) 1 0 (fun st _ => st ⟨(j.val / 5) * 10 + 2 * (j.val % 5), by omega⟩) :=
      HasCirc.proj _
    have hi2 : HasCirc (q * 10 + n) 1 0 (fun st _ => st ⟨(j.val / 5) * 10 + (2 * (j.val % 5) + 1), by omega⟩) :=
      HasCirc.proj _
    have hyj : HasCirc (q * 10 + n) 1 0 (fun st _ => st ⟨q * 10 + j.val, by omega⟩) :=
      HasCirc.proj _
    exact (HasCirc.or2 hi2 (HasCirc.and2 hi1 (HasCirc.not1 hyj))).weaken (by omega)
  refine (HasCirc.comp hstage1 hrec).weaken (by omega) |>.congr ?_
  intro inp j
  unfold unpackPartner
  dsimp only
  set b := j.val / 5
  set r := j.val % 5
  have h1 : (⟨b * 10 + 2 * r, by omega⟩ : Fin (q * 10 + n)) = Fin.castAdd n ⟨b * 10 + 2 * r, by omega⟩ := rfl
  have h2 : (⟨b * 10 + (2 * r + 1), by omega⟩ : Fin (q * 10 + n)) = Fin.castAdd n ⟨b * 10 + (2 * r + 1), by omega⟩ := rfl
  have h3 : (⟨q * 10 + j.val, by omega⟩ : Fin (q * 10 + n)) = Fin.natAdd (q * 10) j := by
    apply Fin.ext; simp [Fin.natAdd]
  rw [h1, h2, h3, Fin.append_left, Fin.append_left, Fin.append_right]
  have hd1 : (b * 10 + 2 * r) / 10 = b := by omega
  have hm1 : (b * 10 + 2 * r) % 10 = 2 * r := by omega
  have hd2 : (b * 10 + (2 * r + 1)) / 10 = b := by omega
  have hm2 : (b * 10 + (2 * r + 1)) % 10 = 2 * r + 1 := by omega
  simp only [hd1, hm1, hd2, hm2]
  rfl

def xorDotList {n : ℕ} (row v : Fin n → Bool) (l : List (Fin n)) (acc : Bool) : Bool :=
  l.foldl (fun a j => Bool.xor a (row j && v j)) acc

def xorDot {n : ℕ} (row v : Fin n → Bool) : Bool :=
  xorDotList row v (List.finRange n) false

def syndrome {r n : ℕ} (H : Fin r → Fin n → Bool) (v : Fin n → Bool) : Fin r → Bool :=
  fun a => xorDot (H a) v

lemma xorDotList_xor {n : ℕ} (row u v : Fin n → Bool) (l : List (Fin n)) (a b : Bool) :
    xorDotList row (fun j => Bool.xor (u j) (v j)) l (Bool.xor a b) =
      Bool.xor (xorDotList row u l a) (xorDotList row v l b) := by
  induction l generalizing a b with
  | nil => rfl
  | cons j l ih =>
    simp only [xorDotList, List.foldl_cons]
    have hstep : Bool.xor (Bool.xor a b) (row j && Bool.xor (u j) (v j)) =
        Bool.xor (Bool.xor a (row j && u j)) (Bool.xor b (row j && v j)) := by
      cases a <;> cases b <;> cases row j <;> cases u j <;> cases v j <;> rfl
    rw [hstep]
    exact ih _ _

lemma syndrome_xor {r n : ℕ} (H : Fin r → Fin n → Bool) (u v : Fin n → Bool) (a : Fin r) :
    syndrome H (fun j => Bool.xor (u j) (v j)) a = Bool.xor (syndrome H u a) (syndrome H v a) :=
  xorDotList_xor (H a) u v (List.finRange n) false false

lemma xorDotList_not_acc {n : ℕ} (row v : Fin n → Bool) (l : List (Fin n)) (acc : Bool) :
    xorDotList row v l (!acc) = !(xorDotList row v l acc) := by
  induction l generalizing acc with
  | nil => rfl
  | cons j l ih =>
    simp only [xorDotList, List.foldl_cons]
    have hstep : Bool.xor (!acc) (row j && v j) = !(Bool.xor acc (row j && v j)) := by
      cases acc <;> cases row j <;> cases v j <;> rfl
    rw [hstep]
    exact ih _

lemma xorDotList_congr {n : ℕ} (r1 r2 v : Fin n → Bool) (l : List (Fin n)) (acc : Bool)
    (heq : ∀ j ∈ l, r1 j = r2 j) :
    xorDotList r1 v l acc = xorDotList r2 v l acc := by
  induction l generalizing acc with
  | nil => rfl
  | cons j l ih =>
    simp only [xorDotList, List.foldl_cons]
    rw [heq j (List.mem_cons_self ..)]
    exact ih _ (fun k hk => heq k (List.mem_cons_of_mem _ hk))

lemma xorDotList_toggle {n : ℕ} (row v : Fin n → Bool) (i₀ : Fin n) (hv : v i₀ = true)
    (l : List (Fin n)) (hnodup : l.Nodup) (hmem : i₀ ∈ l) (acc : Bool) :
    xorDotList (fun j => if j = i₀ then !(row j) else row j) v l acc =
      !(xorDotList row v l acc) := by
  induction l generalizing acc with
  | nil => simp at hmem
  | cons j l ih =>
    rw [List.nodup_cons] at hnodup
    simp only [xorDotList, List.foldl_cons]
    by_cases hji : j = i₀
    · subst hji
      simp only [↓reduceIte, hv, Bool.and_true]
      have hstep : Bool.xor acc (!(row j)) = !(Bool.xor acc (row j)) := by
        cases acc <;> cases row j <;> rfl
      rw [hstep]
      change xorDotList (fun j_1 => if j_1 = j then !row j_1 else row j_1) v l (!(Bool.xor acc (row j))) =
        !(xorDotList row v l (Bool.xor acc (row j)))
      rw [xorDotList_not_acc]
      congr 1
      apply xorDotList_congr
      intro k hk
      have hne : k ≠ j := fun h => hnodup.1 (h ▸ hk)
      simp [hne]
    · simp only [hji, ↓reduceIte]
      have hmem' : i₀ ∈ l := (List.mem_cons.mp hmem).resolve_left (Ne.symm hji)
      exact ih hnodup.2 hmem' _

lemma card_xorDot_false {n : ℕ} (hn : 1 ≤ n) (v : Fin n → Bool) (i₀ : Fin n) (hv : v i₀ = true) :
    (Finset.univ.filter (fun row : Fin n → Bool => xorDot row v = false)).card = 2 ^ (n - 1) := by
  set S0 := Finset.univ.filter (fun row : Fin n → Bool => xorDot row v = false)
  set S1 := Finset.univ.filter (fun row : Fin n → Bool => xorDot row v = true)
  let toggle : (Fin n → Bool) → (Fin n → Bool) := fun row j => if j = i₀ then !(row j) else row j
  have hflip : ∀ row, xorDot (toggle row) v = !(xorDot row v) := fun row =>
    xorDotList_toggle row v i₀ hv (List.finRange n) (List.nodup_finRange n) (List.mem_finRange i₀) false
  have hcard_eq : S0.card = S1.card := by
    refine Finset.card_bij (fun row _ => toggle row) ?_ ?_ ?_
    · intro row hrow
      simp only [S0, S1, Finset.mem_filter, Finset.mem_univ, true_and] at hrow ⊢
      rw [hflip, hrow]; rfl
    · intro r1 _ r2 _ heq
      funext j
      have hj := congrFun heq j
      dsimp [toggle] at hj
      by_cases hji : j = i₀
      · simp only [hji, ↓reduceIte] at hj
        cases h1 : r1 j <;> cases h2 : r2 j <;> simp_all
      · simp only [hji, ↓reduceIte] at hj; exact hj
    · intro row hrow
      refine ⟨toggle row, ?_, ?_⟩
      · simp only [S0, S1, Finset.mem_filter, Finset.mem_univ, true_and] at hrow ⊢
        rw [hflip, hrow]; rfl
      · funext j; dsimp [toggle]; split_ifs <;> simp
  have htot : S0.card + S1.card = 2 ^ n := by
    have hunion : S0 ∪ S1 = Finset.univ := by
      ext row
      simp only [S0, S1, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      cases xorDot row v <;> simp
    have hdisj : Disjoint S0 S1 := by
      rw [Finset.disjoint_left]
      intro row h0 h1
      simp only [S0, S1, Finset.mem_filter, Finset.mem_univ, true_and] at h0 h1
      rw [h0] at h1; exact Bool.noConfusion h1
    rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ, Fintype.card_fun,
      Fintype.card_bool, Fintype.card_fin]
  have hpow : 2 ^ n = 2 * 2 ^ (n - 1) := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega, pow_succ]
    ring
  omega

lemma card_popcount_eq (n j : ℕ) :
    (Finset.univ.filter (fun v : Fin n → Bool => popcountVal v = j)).card = n.choose j := by
  have hbij : (Finset.univ.filter (fun v : Fin n → Bool => popcountVal v = j)).card =
      ((Finset.univ : Finset (Fin n)).powersetCard j).card := by
    refine Finset.card_bij (fun v _ => Finset.univ.filter (fun i : Fin n => v i = true)) ?_ ?_ ?_
    · intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_powersetCard,
        Finset.subset_univ] at hv ⊢
      rw [← popcountVal_eq_card]; exact hv
    · intro v1 _ v2 _ heq
      funext i
      have hi : i ∈ Finset.univ.filter (fun k => v1 k = true) ↔
          i ∈ Finset.univ.filter (fun k => v2 k = true) := by rw [heq]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      cases h1 : v1 i <;> cases h2 : v2 i <;> simp_all
    · intro s hs
      simp only [Finset.mem_powersetCard, Finset.subset_univ, true_and] at hs
      refine ⟨fun i => decide (i ∈ s), ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [popcountVal_eq_card]
        have : Finset.univ.filter (fun i : Fin n => decide (i ∈ s) = true) = s := by
          ext i; simp
        rw [this]; exact hs
      · ext i; simp
  rw [hbij, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

lemma card_popcount_le (n m : ℕ) :
    (Finset.univ.filter (fun v : Fin n → Bool => popcountVal v ≤ m)).card =
      ∑ j ∈ Finset.range (m + 1), n.choose j := by
  have hpart : Finset.univ.filter (fun v : Fin n → Bool => popcountVal v ≤ m) =
      (Finset.range (m + 1)).biUnion (fun j => Finset.univ.filter (fun v : Fin n → Bool => popcountVal v = j)) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, Finset.mem_range]
    constructor
    · intro h; exact ⟨popcountVal v, by omega, rfl⟩
    · rintro ⟨j, hj, rfl⟩; omega
  rw [hpart, Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro j _
    exact card_popcount_eq n j
  · intro j1 _ j2 _ hne
    dsimp [Function.onFun]
    rw [Finset.disjoint_left]
    intro v h1 h2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    exact hne (h1.symm.trans h2)

lemma gv_binom_bound (n : ℕ) (hn : 1 ≤ n) :
    ∑ j ∈ Finset.range (n / 16 + 1), n.choose j < 2 ^ ((3 * n + 7) / 8) := by
  set m := n / 16
  set r := (3 * n + 7) / 8
  set S := ∑ j ∈ Finset.range (m + 1), n.choose j
  have hbin : ∑ j ∈ Finset.range (n + 1), 1 ^ j * 15 ^ (n - j) * n.choose j = (1 + 15) ^ n :=
    (add_pow 1 15 n).symm
  have hsub : Finset.range (m + 1) ⊆ Finset.range (n + 1) :=
    Finset.range_mono (by omega)
  have hle1 : 15 ^ (n - m) * S ≤ 16 ^ n := by
    calc 15 ^ (n - m) * S
        = ∑ j ∈ Finset.range (m + 1), 15 ^ (n - m) * n.choose j := Finset.mul_sum ..
      _ ≤ ∑ j ∈ Finset.range (m + 1), 1 ^ j * 15 ^ (n - j) * n.choose j := by
          apply Finset.sum_le_sum
          intro j hj
          simp only [Finset.mem_range] at hj
          simp only [one_pow, one_mul]
          exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) (by omega))
      _ ≤ ∑ j ∈ Finset.range (n + 1), 1 ^ j * 15 ^ (n - j) * n.choose j :=
          Finset.sum_le_sum_of_subset hsub
      _ = 16 ^ n := hbin
  have hconst : (2 : ℕ) ^ 58 < 15 ^ 15 := by decide
  have hpow1 : (2 ^ 58) ^ n < (15 ^ 15) ^ n := Nat.pow_lt_pow_left hconst (by omega)
  have hpow2 : (15 ^ 15) ^ n ≤ (15 ^ (n - m)) ^ 16 := by
    rw [← pow_mul, ← pow_mul]
    exact Nat.pow_le_pow_right (by omega) (by omega)
  have hpow3 : (15 ^ (n - m)) ^ 16 * S ^ 16 ≤ (16 ^ n) ^ 16 := by
    rw [← mul_pow]
    exact Nat.pow_le_pow_left hle1 16
  have hSpos : 1 ≤ S := by
    have h0 : 0 ∈ Finset.range (m + 1) := Finset.mem_range.mpr (by omega)
    calc 1 = n.choose 0 := (Nat.choose_zero_right n).symm
      _ ≤ S := Finset.single_le_sum (fun _ _ => Nat.zero_le _) h0
  have hS16pos : 0 < S ^ 16 := Nat.pos_of_ne_zero (by positivity)
  have hlt1 : (2 ^ 58) ^ n * S ^ 16 < (16 ^ n) ^ 16 := by
    calc (2 ^ 58) ^ n * S ^ 16
        < (15 ^ 15) ^ n * S ^ 16 := Nat.mul_lt_mul_of_pos_right hpow1 hS16pos
      _ ≤ (15 ^ (n - m)) ^ 16 * S ^ 16 := Nat.mul_le_mul_right _ hpow2
      _ ≤ (16 ^ n) ^ 16 := hpow3
  have h16eq : (16 ^ n) ^ 16 = (2 ^ 58) ^ n * 2 ^ (6 * n) := by
    rw [show (16 : ℕ) = 2 ^ 4 by norm_num, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_add]
    congr 1; ring
  rw [h16eq] at hlt1
  have hS16lt : S ^ 16 < 2 ^ (6 * n) := Nat.lt_of_mul_lt_mul_left hlt1
  have h6le : 2 ^ (6 * n) ≤ (2 ^ r) ^ 16 := by
    rw [← pow_mul]
    exact Nat.pow_le_pow_right (by omega) (by omega)
  have hSlt : S ^ 16 < (2 ^ r) ^ 16 := lt_of_lt_of_le hS16lt h6le
  by_contra hge
  have hle' : 2 ^ r ≤ S := by omega
  exact not_lt_of_ge (Nat.pow_le_pow_left hle' 16) hSlt

lemma gv_matrix_exists (n : ℕ) (hn : 1 ≤ n) :
    let r := (3 * n + 7) / 8
    ∃ H : Fin r → Fin n → Bool,
      ∀ v : Fin n → Bool, (∃ i, v i = true) → popcountVal v ≤ n / 16 →
        syndrome H v ≠ fun _ => false := by
  intro r
  set V := Finset.univ.filter (fun v : Fin n → Bool => (∃ i, v i = true) ∧ popcountVal v ≤ n / 16)
  have hVcard : V.card < 2 ^ r := by
    have hsub : V ⊆ Finset.univ.filter (fun v : Fin n → Bool => popcountVal v ≤ n / 16) := by
      intro v hv; simp only [V, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢; exact hv.2
    calc V.card
        ≤ (Finset.univ.filter (fun v : Fin n → Bool => popcountVal v ≤ n / 16)).card := Finset.card_le_card hsub
      _ = ∑ j ∈ Finset.range (n / 16 + 1), n.choose j := card_popcount_le n (n / 16)
      _ < 2 ^ r := gv_binom_bound n hn
  let badFor (v : Fin n → Bool) : Finset (Fin r → Fin n → Bool) :=
    Finset.univ.filter (fun H => syndrome H v = fun _ => false)
  have hbadCard : ∀ v ∈ V, (badFor v).card = 2 ^ (r * (n - 1)) := by
    intro v hv
    simp only [V, Finset.mem_filter, Finset.mem_univ, true_and] at hv
    rcases hv.1 with ⟨i₀, hi₀⟩
    have hpi : badFor v = Fintype.piFinset (fun _ : Fin r =>
        Finset.univ.filter (fun row : Fin n → Bool => xorDot row v = false)) := by
      ext H
      simp only [badFor, Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset,
        syndrome, funext_iff]
    rw [hpi, Fintype.card_piFinset]
    simp only [card_xorDot_false hn v i₀ hi₀, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      ← pow_mul, Nat.mul_comm]
  set Bad := V.biUnion badFor
  have hBadLt : Bad.card < (Finset.univ : Finset (Fin r → Fin n → Bool)).card := by
    have h1 : Bad.card ≤ ∑ v ∈ V, (badFor v).card := Finset.card_biUnion_le
    have h2 : ∑ v ∈ V, (badFor v).card = V.card * 2 ^ (r * (n - 1)) := by
      rw [Finset.sum_congr rfl hbadCard, Finset.sum_const, smul_eq_mul]
    have h3 : V.card * 2 ^ (r * (n - 1)) < 2 ^ r * 2 ^ (r * (n - 1)) :=
      Nat.mul_lt_mul_of_pos_right hVcard (by positivity)
    have h4 : 2 ^ r * 2 ^ (r * (n - 1)) = 2 ^ (r * n) := by
      rw [← pow_add]
      congr 1
      have : n = (n - 1) + 1 := by omega
      conv_rhs => rw [this, mul_add, mul_one]
      omega
    have huniv : (Finset.univ : Finset (Fin r → Fin n → Bool)).card = 2 ^ (r * n) := by
      rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fun, Fintype.card_bool,
        Fintype.card_fin, Fintype.card_fin, ← pow_mul, Nat.mul_comm]
    omega
  have hne : (Finset.univ \ Bad).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hemp
    have hsub : Finset.univ ⊆ Bad := Finset.sdiff_eq_empty_iff_subset.mp hemp
    exact not_lt_of_ge (Finset.card_le_card hsub) hBadLt
  rcases hne with ⟨H, hH⟩
  rw [Finset.mem_sdiff] at hH
  refine ⟨H, fun v hnz hwt hsyn => hH.2 ?_⟩
  exact Finset.mem_biUnion.mpr ⟨v, by simp [V, hnz, hwt], by simp [badFor, hsyn]⟩

lemma xorDotList_filter {n : ℕ} (row v : Fin n → Bool) (l : List (Fin n)) (acc : Bool) :
    xorDotList row v l acc = (l.filter (fun j => row j)).foldl (fun a j => Bool.xor a (v j)) acc := by
  induction l generalizing acc with
  | nil => rfl
  | cons j l ih =>
    simp only [xorDotList, List.foldl_cons, List.filter_cons]
    cases hr : row j
    · simp only [Bool.false_and, Bool.xor_false, Bool.false_eq_true, ↓reduceIte]
      exact ih acc
    · simp only [Bool.true_and, ↓reduceIte, List.foldl_cons]
      exact ih _

lemma HasCirc.syndromeCirc {r n : ℕ} (hn : 0 < n) (H : Fin r → Fin n → Bool) :
    HasCirc n r (r * (4 * n + 2)) (syndrome H) := by
  apply HasCirc.vecConst (B := 4 * n + 2)
  intro a
  let l := (List.finRange n).filter (fun j => H a j)
  have hlen : l.length ≤ n := by
    calc l.length ≤ (List.finRange n).length := List.length_filter_le _ _
      _ = n := List.length_finRange
  refine (HasCirc.xorList hn l).weaken (by omega) |>.congr ?_
  intro v _
  exact (xorDotList_filter (H a) v (List.finRange n) false).symm

def isRare (n d : ℕ) : Bool :=
  !(decide (16 * Nat.dist (2 * d) n ≤ n))

def tailCount (n : ℕ) : ℕ → ℕ → ℕ
  | 0, w => if isRare n w then 1 else 0
  | m + 1, w => tailCount n m w + tailCount n m (w + 1)

lemma popcountVal_cons {m : ℕ} (b : Bool) (v : Fin m → Bool) :
    popcountVal (Fin.cons b v) = b.toNat + popcountVal v := by
  unfold popcountVal
  rw [Fin.sum_univ_succ]
  simp

lemma tailCount_eq_card (n m w : ℕ) :
    tailCount n m w =
      (Finset.univ.filter (fun v : Fin m → Bool => isRare n (w + popcountVal v) = true)).card := by
  induction m generalizing w with
  | zero =>
    have hpop : ∀ v : Fin 0 → Bool, popcountVal v = 0 := fun _ => by simp [popcountVal]
    simp only [tailCount, hpop, Nat.add_zero]
    cases hr : isRare n w
    · simp
    · simp
  | succ m ih =>
    simp only [tailCount, ih w, ih (w + 1)]
    set S := Finset.univ.filter (fun v : Fin (m + 1) → Bool => isRare n (w + popcountVal v) = true)
    set S0 := S.filter (fun v => v 0 = false)
    set S1 := S.filter (fun v => v 0 = true)
    have hsplit : S.card = S0.card + S1.card := by
      have hunion : S0 ∪ S1 = S := by
        ext v
        simp only [S0, S1, Finset.mem_union, Finset.mem_filter]
        cases v 0 <;> simp
      have hdisj : Disjoint S0 S1 := by
        rw [Finset.disjoint_left]
        intro v h0 h1
        simp only [S0, S1, Finset.mem_filter] at h0 h1
        rw [h0.2] at h1; exact Bool.noConfusion h1.2
      rw [← Finset.card_union_of_disjoint hdisj, hunion]
    have h0 : S0.card = (Finset.univ.filter (fun v : Fin m → Bool => isRare n (w + popcountVal v) = true)).card := by
      symm
      refine Finset.card_bij (fun v _ => Fin.cons false v) ?_ ?_ ?_
      · intro v hv
        simp only [S0, S, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
        rw [popcountVal_cons]; simpa using hv
      · intro v1 _ v2 _ heq
        funext i
        have := congrFun heq i.succ
        simpa using this
      · intro v hv
        simp only [S0, S, Finset.mem_filter, Finset.mem_univ, true_and] at hv
        refine ⟨fun i => v i.succ, ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          have hcons : v = Fin.cons false (fun i => v i.succ) := by
            funext i; refine Fin.cases (by simp [hv.2]) (fun _ => rfl) i
          have hp : popcountVal v = popcountVal (fun i => v i.succ) := by
            conv_lhs => rw [hcons, popcountVal_cons]; simp
          rw [← hp]; exact hv.1
        · funext i; refine Fin.cases (by simp [hv.2]) (fun _ => rfl) i
    have h1 : S1.card = (Finset.univ.filter (fun v : Fin m → Bool => isRare n (w + 1 + popcountVal v) = true)).card := by
      symm
      refine Finset.card_bij (fun v _ => Fin.cons true v) ?_ ?_ ?_
      · intro v hv
        simp only [S1, S, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
        rw [popcountVal_cons]
        have : w + (1 + popcountVal v) = w + 1 + popcountVal v := by omega
        simpa [this] using hv
      · intro v1 _ v2 _ heq
        funext i
        have := congrFun heq i.succ
        simpa using this
      · intro v hv
        simp only [S1, S, Finset.mem_filter, Finset.mem_univ, true_and] at hv
        refine ⟨fun i => v i.succ, ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          have hcons : v = Fin.cons true (fun i => v i.succ) := by
            funext i; refine Fin.cases (by simp [hv.2]) (fun _ => rfl) i
          have hp : popcountVal v = 1 + popcountVal (fun i => v i.succ) := by
            conv_lhs => rw [hcons, popcountVal_cons]; simp
          have : w + 1 + popcountVal (fun i => v i.succ) = w + popcountVal v := by omega
          rw [this]; exact hv.1
        · funext i; refine Fin.cases (by simp [hv.2]) (fun _ => rfl) i
    omega

lemma popcountVal_not {n : ℕ} (v : Fin n → Bool) :
    popcountVal (fun i => !(v i)) + popcountVal v = n := by
  unfold popcountVal
  rw [← Finset.sum_add_distrib]
  have h1 : ∀ i : Fin n, (!(v i)).toNat + (v i).toNat = 1 := fun i => by cases v i <;> rfl
  simp [h1]

lemma chernoff_low_bound (n : ℕ) (hn : 1 ≤ n) :
    ∑ j ∈ Finset.range ((15 * n) / 32 + 1), n.choose j ≤ 2 ^ (n - n / 384) := by
  set d0 := (15 * n) / 32
  set L := ∑ j ∈ Finset.range (d0 + 1), n.choose j
  have hd0 : d0 ≤ n := by omega
  have hbin : ∑ j ∈ Finset.range (n + 1), 15 ^ j * 17 ^ (n - j) * n.choose j = (15 + 17) ^ n :=
    (add_pow 15 17 n).symm
  have hsub : Finset.range (d0 + 1) ⊆ Finset.range (n + 1) := Finset.range_mono (by omega)
  have hterm : ∀ j ≤ d0, 15 ^ d0 * 17 ^ (n - d0) ≤ 15 ^ j * 17 ^ (n - j) := by
    intro j hj
    have hd : d0 = j + (d0 - j) := by omega
    have hn' : n - j = (d0 - j) + (n - d0) := by omega
    calc 15 ^ d0 * 17 ^ (n - d0)
        = 15 ^ j * 15 ^ (d0 - j) * 17 ^ (n - d0) := by
          have h15 : 15 ^ d0 = 15 ^ j * 15 ^ (d0 - j) := by rw [← pow_add, ← hd]
          rw [h15]
      _ ≤ 15 ^ j * 17 ^ (d0 - j) * 17 ^ (n - d0) := by
          gcongr; omega
      _ = 15 ^ j * 17 ^ (n - j) := by
          have h17 : 17 ^ (n - j) = 17 ^ (d0 - j) * 17 ^ (n - d0) := by rw [← pow_add, ← hn']
          rw [h17]; ring
  have hle1 : 15 ^ d0 * 17 ^ (n - d0) * L ≤ 32 ^ n := by
    calc 15 ^ d0 * 17 ^ (n - d0) * L
        = ∑ j ∈ Finset.range (d0 + 1), 15 ^ d0 * 17 ^ (n - d0) * n.choose j := Finset.mul_sum ..
      _ ≤ ∑ j ∈ Finset.range (d0 + 1), 15 ^ j * 17 ^ (n - j) * n.choose j := by
          apply Finset.sum_le_sum
          intro j hj
          simp only [Finset.mem_range] at hj
          exact Nat.mul_le_mul_right _ (hterm j (by omega))
      _ ≤ ∑ j ∈ Finset.range (n + 1), 15 ^ j * 17 ^ (n - j) * n.choose j :=
          Finset.sum_le_sum_of_subset hsub
      _ = 32 ^ n := by simpa using hbin
  have hpow32 : (17 ^ 17 * 15 ^ 15) ^ n ≤ (15 ^ d0 * 17 ^ (n - d0)) ^ 32 := by
    set δ := 15 * n - 32 * d0
    have h15 : 15 * n = 32 * d0 + δ := by omega
    have h17 : 32 * (n - d0) = 17 * n + δ := by omega
    rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul]
    rw [Nat.mul_comm d0 32, Nat.mul_comm (n - d0) 32, h15, h17, pow_add, pow_add]
    calc 17 ^ (17 * n) * (15 ^ (32 * d0) * 15 ^ δ)
        ≤ 17 ^ (17 * n) * (15 ^ (32 * d0) * 17 ^ δ) := by gcongr; omega
      _ = 15 ^ (32 * d0) * (17 ^ (17 * n) * 17 ^ δ) := by ring
  have hconst : (2 : ℕ) ^ 1537 ≤ (17 ^ 17 * 15 ^ 15) ^ 12 := by
    have hsplit : (2 : ℕ) ^ 1537 = 2 * (2 ^ 128) ^ 12 := by
      rw [← pow_mul, ← pow_succ']
    rw [hsplit]
    norm_num
  have hpow384 : (2 ^ 1537) ^ n * L ^ 384 ≤ (32 ^ n) ^ 384 := by
    have hstep1 : (2 ^ 1537) ^ n ≤ ((17 ^ 17 * 15 ^ 15) ^ 12) ^ n :=
      Nat.pow_le_pow_left hconst n
    have hstep2 : ((17 ^ 17 * 15 ^ 15) ^ 12) ^ n ≤ ((15 ^ d0 * 17 ^ (n - d0)) ^ 32) ^ 12 := by
      rw [← pow_mul, Nat.mul_comm 12 n, pow_mul]
      exact Nat.pow_le_pow_left hpow32 12
    have hstep3 : ((15 ^ d0 * 17 ^ (n - d0)) ^ 32) ^ 12 * L ^ 384 ≤ (32 ^ n) ^ 384 := by
      rw [← pow_mul, show 32 * 12 = 384 by norm_num, ← mul_pow]
      exact Nat.pow_le_pow_left hle1 384
    exact le_trans (Nat.mul_le_mul_right _ (le_trans hstep1 hstep2)) hstep3
  have h32eq : (32 ^ n) ^ 384 = (2 ^ 1537) ^ n * 2 ^ (383 * n) := by
    rw [show (32 : ℕ) = 2 ^ 5 by norm_num, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_add]
    congr 1; ring
  rw [h32eq] at hpow384
  have hL384 : L ^ 384 ≤ 2 ^ (383 * n) := Nat.le_of_mul_le_mul_left hpow384 (by positivity)
  have hexp : 383 * n ≤ 384 * (n - n / 384) := by omega
  have hLle : L ^ 384 ≤ (2 ^ (n - n / 384)) ^ 384 := by
    rw [← pow_mul, Nat.mul_comm (n - n / 384) 384]
    exact le_trans hL384 (Nat.pow_le_pow_right (by omega) hexp)
  by_contra hgt
  have hlt : 2 ^ (n - n / 384) < L := by omega
  exact not_lt_of_ge hLle (Nat.pow_lt_pow_left hlt (by omega))

lemma tailCount_top_lt (n : ℕ) (hn : 1 ≤ n) :
    tailCount n n 0 < 2 ^ (n - n / 384 + 2) := by
  rw [tailCount_eq_card]
  simp only [Nat.zero_add]
  set Low := Finset.univ.filter (fun v : Fin n → Bool => 32 * popcountVal v < 15 * n)
  set High := Finset.univ.filter (fun v : Fin n → Bool => 32 * (n - popcountVal v) < 15 * n)
  have hsub : Finset.univ.filter (fun v : Fin n → Bool => isRare n (popcountVal v) = true) ⊆ Low ∪ High := by
    intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, isRare, Bool.not_eq_true',
      decide_eq_false_iff_not] at hv
    have hle := popcountVal_le v
    have hiff := band_iff_interval n (popcountVal v)
    have hnot : ¬ ((15 * n + 31) / 32 ≤ popcountVal v ∧ popcountVal v ≤ (17 * n) / 32) :=
      fun h => hv (hiff.mpr h)
    simp only [Low, High, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have hHighEq : High.card = Low.card := by
    refine Finset.card_bij (fun v _ => fun i => !(v i)) ?_ ?_ ?_
    · intro v hv
      simp only [High, Low, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
      have hnp := popcountVal_not v
      have : popcountVal (fun i => !(v i)) = n - popcountVal v := by omega
      rw [this]; exact hv
    · intro v1 _ v2 _ heq
      funext i
      have hi := congrFun heq i
      cases h1 : v1 i <;> cases h2 : v2 i <;> simp_all
    · intro v hv
      refine ⟨fun i => !(v i), ?_, by funext i; simp⟩
      simp only [High, Low, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
      have hnp := popcountVal_not v
      have : n - popcountVal (fun i => !(v i)) = popcountVal v := by omega
      rw [this]; exact hv
  have hLowLe : Low.card ≤ 2 ^ (n - n / 384) := by
    have hsub2 : Low ⊆ Finset.univ.filter (fun v : Fin n → Bool => popcountVal v ≤ (15 * n) / 32) := by
      intro v hv
      simp only [Low, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
      omega
    calc Low.card
        ≤ (Finset.univ.filter (fun v : Fin n → Bool => popcountVal v ≤ (15 * n) / 32)).card :=
          Finset.card_le_card hsub2
      _ = ∑ j ∈ Finset.range ((15 * n) / 32 + 1), n.choose j := card_popcount_le n ((15 * n) / 32)
      _ ≤ 2 ^ (n - n / 384) := chernoff_low_bound n hn
  have hcard : (Finset.univ.filter (fun v : Fin n → Bool => isRare n (popcountVal v) = true)).card ≤
      2 * 2 ^ (n - n / 384) := by
    calc (Finset.univ.filter (fun v : Fin n → Bool => isRare n (popcountVal v) = true)).card
        ≤ (Low ∪ High).card := Finset.card_le_card hsub
      _ ≤ Low.card + High.card := Finset.card_union_le Low High
      _ = 2 * Low.card := by omega
      _ ≤ 2 * 2 ^ (n - n / 384) := by omega
  have hpow : 2 ^ (n - n / 384 + 2) = 4 * 2 ^ (n - n / 384) := by
    rw [pow_add]; ring
  have hpos : 0 < 2 ^ (n - n / 384) := by positivity
  omega

lemma tailCount_le_top (n : ℕ) :
    ∀ i ≤ n, ∀ w ≤ i, tailCount n (n - i) w ≤ tailCount n n 0 := by
  intro i hi
  induction i with
  | zero =>
    intro w hw
    have hw0 : w = 0 := by omega
    subst hw0
    simp
  | succ i ih =>
    intro w hw
    have hstep : n - i = (n - (i + 1)) + 1 := by omega
    by_cases hwi : w ≤ i
    · have h1 := ih (by omega) w hwi
      rw [hstep, tailCount] at h1
      omega
    · have hweq : w = i + 1 := by omega
      subst hweq
      have h1 := ih (by omega) i le_rfl
      rw [hstep, tailCount] at h1
      omega

lemma tailCount_step_lt (n : ℕ) (hn : 1 ≤ n) (i : Fin n) (w : ℕ) (hw : w ≤ i.val) :
    tailCount n (n - 1 - i.val) w < 2 ^ (n - n / 384 + 2) := by
  have hle : tailCount n (n - 1 - i.val) w ≤ tailCount n n 0 := by
    have h1 := tailCount_le_top n (i.val + 1) (by omega) w (by omega)
    have heq : n - (i.val + 1) = n - 1 - i.val := by omega
    rwa [heq] at h1
  exact lt_of_le_of_lt hle (tailCount_top_lt n hn)

def suffixPop (n : ℕ) (u : Fin n → Bool) : (m : ℕ) → m ≤ n → ℕ
  | 0, _ => 0
  | m + 1, hm => (u ⟨n - 1 - m, by omega⟩).toNat + suffixPop n u m (by omega)

def rankFrom (n : ℕ) (u : Fin n → Bool) : (m : ℕ) → m ≤ n → ℕ → ℕ
  | 0, _, _ => 0
  | m + 1, hm, w =>
    let b := u ⟨n - 1 - m, by omega⟩
    (if b then tailCount n m w else 0) + rankFrom n u m (by omega) (w + b.toNat)

lemma rankFrom_lt (n : ℕ) (u : Fin n → Bool) (m : ℕ) (hm : m ≤ n) (w : ℕ)
    (hr : isRare n (w + suffixPop n u m hm) = true) :
    rankFrom n u m hm w < tailCount n m w := by
  induction m generalizing w with
  | zero =>
    simp only [suffixPop, Nat.add_zero] at hr
    simp [rankFrom, tailCount, hr]
  | succ m ih =>
    simp only [suffixPop] at hr
    simp only [rankFrom, tailCount]
    cases hb : u ⟨n - 1 - m, by omega⟩
    · simp only [hb, Bool.toNat_false, Nat.zero_add, Nat.add_zero, Bool.false_eq_true, ↓reduceIte] at hr ⊢
      have h1 := ih (by omega) w hr
      omega
    · simp only [hb, Bool.toNat_true, ↓reduceIte] at hr ⊢
      have hr' : isRare n ((w + 1) + suffixPop n u m (by omega)) = true := by
        have : (w + 1) + suffixPop n u m (by omega) = w + (1 + suffixPop n u m (by omega)) := by omega
        rwa [this]
      have h1 := ih (by omega) (w + 1) hr'
      omega

def rankStep (n : ℕ) (u : Fin n → Bool) (st : ℕ × ℕ) (i : Fin n) : ℕ × ℕ :=
  if u i then (st.1 + 1, st.2 + tailCount n (n - 1 - i.val) st.1) else st

def rankFold (n : ℕ) (u : Fin n → Bool) : ℕ :=
  ((List.finRange n).foldl (rankStep n u) (0, 0)).2

def unrankStep (n : ℕ) (st : ℕ × ℕ × (Fin n → Bool)) (i : Fin n) : ℕ × ℕ × (Fin n → Bool) :=
  let T := tailCount n (n - 1 - i.val) st.1
  if T ≤ st.2.1 then
    (st.1 + 1, st.2.1 - T, fun j => if j = i then true else st.2.2 j)
  else
    (st.1, st.2.1, fun j => if j = i then false else st.2.2 j)

def unrankFold (n : ℕ) (r : ℕ) : Fin n → Bool :=
  ((List.finRange n).foldl (unrankStep n) (0, r, fun _ => false)).2.2

lemma take_succ_finRange {n t : ℕ} (ht : t < n) :
    (List.finRange n).take (t + 1) = (List.finRange n).take t ++ [⟨t, ht⟩] := by
  rw [List.take_succ_eq_append_getElem (by simp [ht])]
  simp

lemma rankPrefix_inv (n : ℕ) (u : Fin n → Bool) (t : ℕ) (ht : t ≤ n) :
    let st := ((List.finRange n).take t).foldl (rankStep n u) (0, 0)
    st.1 ≤ t ∧
    st.1 + suffixPop n u (n - t) (by omega) = suffixPop n u n le_rfl ∧
    st.2 + rankFrom n u (n - t) (by omega) st.1 = rankFrom n u n le_rfl 0 := by
  induction t with
  | zero =>
    simp
  | succ t ih =>
    rcases ih (by omega) with ⟨hw, hpop, hrank⟩
    set st := ((List.finRange n).take t).foldl (rankStep n u) (0, 0) with hst
    have htake := take_succ_finRange (n := n) (t := t) (by omega)
    dsimp only
    rw [htake, List.foldl_append, List.foldl_cons, List.foldl_nil, ← hst]
    have hsub : n - t = (n - (t + 1)) + 1 := by omega
    have hidx : (⟨n - 1 - (n - (t + 1)), by omega⟩ : Fin n) = ⟨t, by omega⟩ := by
      apply Fin.ext; simp; omega
    have hpop_step : suffixPop n u (n - t) (by omega) =
        (u ⟨t, by omega⟩).toNat + suffixPop n u (n - (t + 1)) (by omega) := by
      have hm : ∀ (m : ℕ) (hm : m ≤ n) (h : m = (n - (t + 1)) + 1),
          suffixPop n u m hm = (u ⟨t, by omega⟩).toNat + suffixPop n u (n - (t + 1)) (by omega) := by
        intro m hm h; subst h; simp only [suffixPop, hidx]
      exact hm (n - t) (by omega) hsub
    have hrank_step : rankFrom n u (n - t) (by omega) st.1 =
        (if u ⟨t, by omega⟩ then tailCount n (n - 1 - t) st.1 else 0) +
          rankFrom n u (n - (t + 1)) (by omega) (st.1 + (u ⟨t, by omega⟩).toNat) := by
      have hm : ∀ (m : ℕ) (hm : m ≤ n) (h : m = (n - (t + 1)) + 1),
          rankFrom n u m hm st.1 =
            (if u ⟨t, by omega⟩ then tailCount n (n - 1 - t) st.1 else 0) +
              rankFrom n u (n - (t + 1)) (by omega) (st.1 + (u ⟨t, by omega⟩).toNat) := by
        intro m hm h; subst h
        simp only [rankFrom, hidx]
        have htc : tailCount n (n - (t + 1)) st.1 = tailCount n (n - 1 - t) st.1 := by
          congr 1; omega
        rw [htc]
      exact hm (n - t) (by omega) hsub
    unfold rankStep
    cases hu : u ⟨t, by omega⟩
    · simp only [hu, Bool.false_eq_true, ↓reduceIte] at hpop_step hrank_step ⊢
      simp only [Bool.toNat_false, Nat.zero_add, Nat.add_zero] at hpop_step hrank_step
      refine ⟨by omega, by omega, by omega⟩
    · simp only [hu, ↓reduceIte] at hpop_step hrank_step ⊢
      simp only [Bool.toNat_true] at hpop_step hrank_step
      refine ⟨by omega, by omega, by omega⟩

lemma suffixPop_eq_popcount (n : ℕ) (u : Fin n → Bool) :
    suffixPop n u n le_rfl = popcountVal u := by
  have h : ∀ t ≤ n,
      (∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < t), (u j).toNat) +
        suffixPop n u (n - t) (by omega) = suffixPop n u n le_rfl := by
    intro t ht
    induction t with
    | zero => simp
    | succ t ih =>
      have h1 := ih (by omega)
      have hsub : n - t = (n - (t + 1)) + 1 := by omega
      have hidx : (⟨n - 1 - (n - (t + 1)), by omega⟩ : Fin n) = ⟨t, by omega⟩ := by
        apply Fin.ext; simp; omega
      have hpop_step : suffixPop n u (n - t) (by omega) =
          (u ⟨t, by omega⟩).toNat + suffixPop n u (n - (t + 1)) (by omega) := by
        have hm : ∀ (m : ℕ) (hm : m ≤ n) (heq : m = (n - (t + 1)) + 1),
            suffixPop n u m hm = (u ⟨t, by omega⟩).toNat + suffixPop n u (n - (t + 1)) (by omega) := by
          intro m hm heq; subst heq; simp only [suffixPop, hidx]
        exact hm (n - t) (by omega) hsub
      have hfilt : Finset.univ.filter (fun j : Fin n => j.val < t + 1) =
          insert ⟨t, by omega⟩ (Finset.univ.filter (fun j : Fin n => j.val < t)) := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
        omega
      have hnotmem : (⟨t, by omega⟩ : Fin n) ∉ Finset.univ.filter (fun j : Fin n => j.val < t) := by
        simp
      rw [hfilt, Finset.sum_insert hnotmem]
      omega
  have hn := h n le_rfl
  simp only [Nat.sub_self, suffixPop, Nat.add_zero] at hn
  have huniv : Finset.univ.filter (fun j : Fin n => j.val < n) = Finset.univ := by
    ext j; simp [j.isLt]
  rw [huniv] at hn
  exact hn.symm

lemma rankFold_lt (n : ℕ) (u : Fin n → Bool) (hr : isRare n (popcountVal u) = true) :
    rankFold n u < tailCount n n 0 := by
  have hinv := rankPrefix_inv n u n le_rfl
  have htake : (List.finRange n).take n = List.finRange n := by simp
  simp only [htake, Nat.sub_self, rankFrom, Nat.add_zero] at hinv
  unfold rankFold
  rw [hinv.2.2]
  apply rankFrom_lt
  rw [Nat.zero_add, suffixPop_eq_popcount]
  exact hr

lemma unrankPrefix_inv (n : ℕ) (u : Fin n → Bool) (hr : isRare n (popcountVal u) = true)
    (t : ℕ) (ht : t ≤ n) :
    let rst := ((List.finRange n).take t).foldl (rankStep n u) (0, 0)
    let ust := ((List.finRange n).take t).foldl (unrankStep n) (0, rankFold n u, fun _ => false)
    ust.1 = rst.1 ∧
    ust.2.1 = rankFrom n u (n - t) (by omega) rst.1 ∧
    ∀ j : Fin n, j.val < t → ust.2.2 j = u j := by
  induction t with
  | zero =>
    simp only [List.take_zero, List.foldl_nil, Nat.sub_zero, true_and]
    have hinv := rankPrefix_inv n u n le_rfl
    have htake : (List.finRange n).take n = List.finRange n := by simp
    simp only [htake, Nat.sub_self, rankFrom, Nat.add_zero] at hinv
    refine ⟨?_, fun j hj => by omega⟩
    unfold rankFold
    exact hinv.2.2
  | succ t ih =>
    rcases ih (by omega) with ⟨hw, hrem, hout⟩
    rcases rankPrefix_inv n u t (by omega) with ⟨hwle, hpop, _⟩
    set rst := ((List.finRange n).take t).foldl (rankStep n u) (0, 0) with hrst
    set ust := ((List.finRange n).take t).foldl (unrankStep n) (0, rankFold n u, fun _ => false) with hust
    have htake := take_succ_finRange (n := n) (t := t) (by omega)
    dsimp only
    rw [htake, List.foldl_append, List.foldl_cons, List.foldl_nil,
      List.foldl_append, List.foldl_cons, List.foldl_nil, ← hrst, ← hust]
    have hsub : n - t = (n - (t + 1)) + 1 := by omega
    have hidx : (⟨n - 1 - (n - (t + 1)), by omega⟩ : Fin n) = ⟨t, by omega⟩ := by
      apply Fin.ext; simp; omega
    have hpop_step : suffixPop n u (n - t) (by omega) =
        (u ⟨t, by omega⟩).toNat + suffixPop n u (n - (t + 1)) (by omega) := by
      have hm : ∀ (m : ℕ) (hm : m ≤ n) (h : m = (n - (t + 1)) + 1),
          suffixPop n u m hm = (u ⟨t, by omega⟩).toNat + suffixPop n u (n - (t + 1)) (by omega) := by
        intro m hm h; subst h; simp only [suffixPop, hidx]
      exact hm (n - t) (by omega) hsub
    have hrank_step : rankFrom n u (n - t) (by omega) rst.1 =
        (if u ⟨t, by omega⟩ then tailCount n (n - 1 - t) rst.1 else 0) +
          rankFrom n u (n - (t + 1)) (by omega) (rst.1 + (u ⟨t, by omega⟩).toNat) := by
      have hm : ∀ (m : ℕ) (hm : m ≤ n) (h : m = (n - (t + 1)) + 1),
          rankFrom n u m hm rst.1 =
            (if u ⟨t, by omega⟩ then tailCount n (n - 1 - t) rst.1 else 0) +
              rankFrom n u (n - (t + 1)) (by omega) (rst.1 + (u ⟨t, by omega⟩).toNat) := by
        intro m hm h; subst h
        simp only [rankFrom, hidx]
        have htc : tailCount n (n - (t + 1)) rst.1 = tailCount n (n - 1 - t) rst.1 := by
          congr 1; omega
        rw [htc]
      exact hm (n - t) (by omega) hsub
    have hr_cur : isRare n (rst.1 + suffixPop n u (n - t) (by omega)) = true := by
      rw [hpop, suffixPop_eq_popcount]; exact hr
    unfold unrankStep rankStep
    dsimp only
    rw [hw, hrem, hrank_step]
    cases hu : u ⟨t, by omega⟩
    · simp only [hu, Bool.false_eq_true, ↓reduceIte, Bool.toNat_false, Nat.zero_add, Nat.add_zero] at hr_cur hpop_step ⊢
      have hr_next : isRare n (rst.1 + suffixPop n u (n - (t + 1)) (by omega)) = true := by
        rw [hpop_step] at hr_cur; exact hr_cur
      have hlt : rankFrom n u (n - (t + 1)) (by omega) rst.1 < tailCount n (n - 1 - t) rst.1 := by
        have h1 := rankFrom_lt n u (n - (t + 1)) (by omega) rst.1 hr_next
        have htc : tailCount n (n - (t + 1)) rst.1 = tailCount n (n - 1 - t) rst.1 := by
          congr 1; omega
        rwa [htc] at h1
      have hnotle : ¬ (tailCount n (n - 1 - t) rst.1 ≤ rankFrom n u (n - (t + 1)) (by omega) rst.1) := by omega
      simp only [hnotle, ↓reduceIte, true_and]
      intro j hj
      by_cases hjt : j = ⟨t, by omega⟩
      · rw [hjt]; simp [hu]
      · simp only [hjt, ↓reduceIte]
        have hjlt : j.val < t := by
          have : j.val ≠ t := fun h => hjt (Fin.ext h)
          omega
        exact hout j hjlt
    · simp only [hu, ↓reduceIte, Bool.toNat_true]
      have hle : tailCount n (n - 1 - t) rst.1 ≤
          tailCount n (n - 1 - t) rst.1 + rankFrom n u (n - (t + 1)) (by omega) (rst.1 + 1) := by omega
      simp only [hle, ↓reduceIte, Nat.add_sub_cancel_left, true_and]
      intro j hj
      by_cases hjt : j = ⟨t, by omega⟩
      · rw [hjt]; simp [hu]
      · simp only [hjt, ↓reduceIte]
        have hjlt : j.val < t := by
          have : j.val ≠ t := fun h => hjt (Fin.ext h)
          omega
        exact hout j hjlt

lemma unrankFold_rankFold (n : ℕ) (u : Fin n → Bool) (hr : isRare n (popcountVal u) = true) :
    unrankFold n (rankFold n u) = u := by
  have hinv := unrankPrefix_inv n u hr n le_rfl
  have htake : (List.finRange n).take n = List.finRange n := by simp
  simp only [htake] at hinv
  funext j
  exact hinv.2.2 j j.isLt

def oneHot (n w : ℕ) : Fin (n + 1) → Bool :=
  fun i => decide (i.val = w)

def oneHotLookupFun (n B : ℕ) (tbl : Fin (n + 1) → ℕ) (oh : Fin (n + 1) → Bool) : Fin B → Bool :=
  fun b => ((List.finRange (n + 1)).filter (fun w => (tbl w).testBit b.val)).foldl
    (fun acc w => acc || oh w) false

lemma foldl_or_eq_any {α : Type} (l : List α) (p : α → Bool) (init : Bool) :
    l.foldl (fun acc x => acc || p x) init = (init || l.any p) := by
  induction l generalizing init with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldl_cons, List.any_cons, ih, Bool.or_assoc]

lemma oneHotLookup_spec (n B : ℕ) (tbl : Fin (n + 1) → ℕ) (w₀ : ℕ) (hw : w₀ ≤ n) :
    oneHotLookupFun n B tbl (oneHot n w₀) = natToBits B (tbl ⟨w₀, by omega⟩) := by
  funext b
  unfold oneHotLookupFun oneHot natToBits
  rw [foldl_or_eq_any]
  simp only [Bool.false_or]
  cases ht : (tbl ⟨w₀, by omega⟩).testBit b.val
  · simp only [List.any_eq_false, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]
    intro w htb hweq
    have hwf : w = ⟨w₀, by omega⟩ := Fin.ext hweq
    rw [hwf, ht] at htb
    exact Bool.noConfusion htb
  · simp only [List.any_eq_true, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]
    exact ⟨⟨w₀, by omega⟩, ht, rfl⟩

lemma HasCirc.oneHotLookup (n B : ℕ) (tbl : Fin (n + 1) → ℕ) :
    HasCirc (n + 1) B (B * (n + 3)) (oneHotLookupFun n B tbl) := by
  apply HasCirc.vecConst (B := n + 3)
  intro b
  let l := (List.finRange (n + 1)).filter (fun w => (tbl w).testBit b.val)
  have hlen : l.length ≤ n + 1 := by
    calc l.length ≤ (List.finRange (n + 1)).length := List.length_filter_le _ _
      _ = n + 1 := List.length_finRange
  exact (HasCirc.orList (by omega) l).weaken (by omega)

def oneHotShiftFun (n : ℕ) (x : Fin (1 + (n + 1)) → Bool) : Fin (n + 1) → Bool :=
  fun w =>
    let b := x ⟨0, by omega⟩
    if h : w.val = 0 then (!b) && x ⟨1, by omega⟩
    else if b then x ⟨1 + (w.val - 1), by omega⟩ else x ⟨1 + w.val, by omega⟩

lemma oneHotShift_spec (n w₀ : ℕ) (hw : w₀ < n) (b : Bool) :
    oneHotShiftFun n (Fin.append (fun _ : Fin 1 => b) (oneHot n w₀)) =
      oneHot n (w₀ + b.toNat) := by
  funext w
  unfold oneHotShiftFun oneHot
  have hb : Fin.append (fun _ : Fin 1 => b) (fun i : Fin (n + 1) => decide (i.val = w₀)) ⟨0, by omega⟩ = b := by
    change Fin.append _ _ (Fin.castAdd (n + 1) 0) = b
    rw [Fin.append_left]
  have hget : ∀ (j : Fin (n + 1)),
      Fin.append (fun _ : Fin 1 => b) (fun i : Fin (n + 1) => decide (i.val = w₀)) ⟨1 + j.val, by omega⟩ =
      decide (j.val = w₀) := by
    intro j
    have : (⟨1 + j.val, by omega⟩ : Fin (1 + (n + 1))) = Fin.natAdd 1 j := by
      apply Fin.ext; simp [Fin.natAdd]
    rw [this, Fin.append_right]
  rw [hb]
  by_cases hw0 : w.val = 0
  · simp only [hw0, ↓reduceDIte]
    have h1 : Fin.append (fun _ : Fin 1 => b) (fun i : Fin (n + 1) => decide (i.val = w₀)) ⟨1, by omega⟩ =
        decide (0 = w₀) := hget ⟨0, by omega⟩
    rw [h1]
    cases b <;> simp
  · simp only [hw0, ↓reduceDIte]
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte, Bool.toNat_false, Nat.add_zero]
      exact hget w
    · simp only [↓reduceIte, Bool.toNat_true]
      rw [hget ⟨w.val - 1, by omega⟩]
      by_cases h : w.val - 1 = w₀
      · have h' : w.val = w₀ + 1 := by omega
        simp [h, h']
      · have h' : w.val ≠ w₀ + 1 := by omega
        simp [h, h']

lemma HasCirc.oneHotShift (n : ℕ) :
    HasCirc (1 + (n + 1)) (n + 1) ((n + 1) * 4) (oneHotShiftFun n) := by
  apply HasCirc.vecConst (B := 4)
  intro w
  have hb : HasCirc (1 + (n + 1)) 1 0 (fun x _ => x ⟨0, by omega⟩) := HasCirc.proj _
  by_cases hw0 : w.val = 0
  · have h0 : HasCirc (1 + (n + 1)) 1 0 (fun x _ => x ⟨1, by omega⟩) := HasCirc.proj _
    refine (HasCirc.and2 (HasCirc.not1 hb) h0).weaken (by omega) |>.congr ?_
    intro x _
    simp [oneHotShiftFun, hw0]
  · have hprev : HasCirc (1 + (n + 1)) 1 0 (fun x _ => x ⟨1 + (w.val - 1), by omega⟩) := HasCirc.proj _
    have hcur : HasCirc (1 + (n + 1)) 1 0 (fun x _ => x ⟨1 + w.val, by omega⟩) := HasCirc.proj _
    refine (HasCirc.ite3 hb hprev hcur).weaken (by omega) |>.congr ?_
    intro x _
    simp [oneHotShiftFun, hw0]

def rankCircStepFun (n B : ℕ) (i : Fin n) (inp : Fin (n + ((n + 1) + B)) → Bool) :
    Fin ((n + 1) + B) → Bool :=
  let bi := inp ⟨i.val, by omega⟩
  let oh : Fin (n + 1) → Bool := fun w => inp ⟨n + w.val, by omega⟩
  let acc : Fin B → Bool := fun b => inp ⟨n + (n + 1) + b.val, by omega⟩
  let T := oneHotLookupFun n B (fun w => tailCount n (n - 1 - i.val) w.val) oh
  let Tmask : Fin B → Bool := fun b => bi && T b
  let sum := addBFun B (Fin.append acc Tmask)
  let oh' := oneHotShiftFun n (Fin.append (fun _ : Fin 1 => bi) oh)
  Fin.append oh' (fun b : Fin B => sum b.castSucc)

lemma HasCirc.rankCircStep (n B : ℕ) (hB : 0 < B) (i : Fin n) :
    HasCirc (n + ((n + 1) + B)) ((n + 1) + B) (B * (n + 3) + 17 * B + 4 * (n + 1) + 2)
      (rankCircStepFun n B i) := by
  set I := n + ((n + 1) + B)
  have hbi : HasCirc I 1 0 (fun inp _ => inp ⟨i.val, by omega⟩) := HasCirc.proj _
  have hoh : HasCirc I (n + 1) 0 (fun inp w => inp ⟨n + w.val, by omega⟩) := HasCirc.proj _
  have hacc : HasCirc I B 0 (fun inp b => inp ⟨n + (n + 1) + b.val, by omega⟩) := HasCirc.proj _
  have hT : HasCirc I B (B * (n + 3))
      (fun inp => oneHotLookupFun n B (fun w => tailCount n (n - 1 - i.val) w.val)
        (fun w => inp ⟨n + w.val, by omega⟩)) :=
    (HasCirc.comp hoh (HasCirc.oneHotLookup n B _)).weaken (by omega)
  have hTmask : HasCirc I B (B * (n + 3) + B)
      (fun inp b => inp ⟨i.val, by omega⟩ &&
        oneHotLookupFun n B (fun w => tailCount n (n - 1 - i.val) w.val)
          (fun w => inp ⟨n + w.val, by omega⟩) b) := by
    have h1 := HasCirc.pair hbi hT
    have h2 : HasCirc (1 + B) B (B * 1) (fun y b => y ⟨0, by omega⟩ && y ⟨1 + b.val, by omega⟩) :=
      HasCirc.vecConst (B := 1) (fun b =>
        (HasCirc.and2 (HasCirc.proj (n := 1 + B) (m := 1) (fun _ => ⟨0, by omega⟩))
          (HasCirc.proj (n := 1 + B) (m := 1) (fun _ => ⟨1 + b.val, by omega⟩))).weaken (by omega))
    refine (HasCirc.comp h1 h2).weaken (by omega) |>.congr ?_
    intro inp b
    have h0 : (⟨0, by omega⟩ : Fin (1 + B)) = Fin.castAdd B 0 := rfl
    have h1' : (⟨1 + b.val, by omega⟩ : Fin (1 + B)) = Fin.natAdd 1 b := by
      apply Fin.ext; simp [Fin.natAdd]
    rw [h0, h1', Fin.append_left, Fin.append_right]
  have hsum : HasCirc I B (B * (n + 3) + B + (16 * B + 2))
      (fun inp b => addBFun B (Fin.append (fun k => inp ⟨n + (n + 1) + k.val, by omega⟩)
        (fun k => inp ⟨i.val, by omega⟩ &&
          oneHotLookupFun n B (fun w => tailCount n (n - 1 - i.val) w.val)
            (fun w => inp ⟨n + w.val, by omega⟩) k)) b.castSucc) := by
    have h1 := HasCirc.comp (HasCirc.pair hacc hTmask) (HasCirc.addB B hB)
    exact (HasCirc.comp h1 (HasCirc.proj Fin.castSucc)).weaken (by omega)
  have hoh' : HasCirc I (n + 1) ((n + 1) * 4)
      (fun inp => oneHotShiftFun n (Fin.append (fun _ : Fin 1 => inp ⟨i.val, by omega⟩)
        (fun w => inp ⟨n + w.val, by omega⟩))) :=
    (HasCirc.comp (HasCirc.pair hbi hoh) (HasCirc.oneHotShift n)).weaken (by omega)
  exact (HasCirc.pair hoh' hsum).weaken (by omega)

def rankCircFun (n B : ℕ) (u : Fin n → Bool) : Fin B → Bool :=
  let init : Fin ((n + 1) + B) → Bool := Fin.append (oneHot n 0) (fun _ => false)
  let final := (List.finRange n).foldl (fun st i => rankCircStepFun n B i (Fin.append u st)) init
  fun b => final (Fin.natAdd (n + 1) b)

lemma rankCircFun_eq (n : ℕ) (hn : 1 ≤ n) (u : Fin n → Bool)
    (hr : isRare n (popcountVal u) = true) :
    let B := n - n / 384 + 2
    rankCircFun n B u = natToBits B (rankFold n u) := by
  intro B
  have hlt_top : tailCount n n 0 < 2 ^ B := tailCount_top_lt n hn
  have htot_lt : rankFrom n u n le_rfl 0 < 2 ^ B := by
    have h1 := rankFrom_lt n u n le_rfl 0 (by rw [Nat.zero_add, suffixPop_eq_popcount]; exact hr)
    exact lt_trans h1 hlt_top
  let init : Fin ((n + 1) + B) → Bool := Fin.append (oneHot n 0) (fun _ => false)
  have hinv : ∀ t ≤ n,
      let st := ((List.finRange n).take t).foldl (rankStep n u) (0, 0)
      ((List.finRange n).take t).foldl (fun s i => rankCircStepFun n B i (Fin.append u s)) init =
        Fin.append (oneHot n st.1) (natToBits B st.2) := by
    intro t ht
    induction t with
    | zero =>
      simp only [List.take_zero, List.foldl_nil, init]
      congr 1; funext b; simp [natToBits]
    | succ t ih =>
      have ih' := ih (by omega)
      rcases rankPrefix_inv n u t (by omega) with ⟨hwle, _, hrank⟩
      rcases rankPrefix_inv n u (t + 1) ht with ⟨_, _, hrank_next⟩
      set st := ((List.finRange n).take t).foldl (rankStep n u) (0, 0) with hst
      have htake := take_succ_finRange (n := n) (t := t) (by omega)
      dsimp only
      rw [htake, List.foldl_append, List.foldl_cons, List.foldl_nil,
        List.foldl_append, List.foldl_cons, List.foldl_nil, ← hst, ih']
      unfold rankCircStepFun rankStep
      dsimp only
      set s_cur := Fin.append (oneHot n st.1) (natToBits B st.2)
      have hbi : Fin.append u s_cur ⟨t, by omega⟩ = u ⟨t, by omega⟩ := by
        change Fin.append u s_cur (Fin.castAdd ((n + 1) + B) ⟨t, by omega⟩) = _
        rw [Fin.append_left]
      have hoh : (fun w : Fin (n + 1) => Fin.append u s_cur ⟨n + w.val, by omega⟩) = oneHot n st.1 := by
        funext w
        have h1 : (⟨n + w.val, by omega⟩ : Fin (n + ((n + 1) + B))) =
            Fin.natAdd n (Fin.castAdd B w) := by apply Fin.ext; simp [Fin.natAdd]
        rw [h1, Fin.append_right]
        dsimp [s_cur]
        rw [Fin.append_left]
      have hacc : (fun b : Fin B => Fin.append u s_cur ⟨n + (n + 1) + b.val, by omega⟩) = natToBits B st.2 := by
        funext b
        have h1 : (⟨n + (n + 1) + b.val, by omega⟩ : Fin (n + ((n + 1) + B))) =
            Fin.natAdd n (Fin.natAdd (n + 1) b) := by apply Fin.ext; simp [Fin.natAdd]; omega
        rw [h1, Fin.append_right]
        dsimp [s_cur]
        rw [Fin.append_right]
      rw [hbi, hoh, hacc]
      rw [oneHotLookup_spec n B _ st.1 (by omega)]
      rw [oneHotShift_spec n st.1 (by omega) (u ⟨t, by omega⟩)]
      have hT_lt : tailCount n (n - 1 - t) st.1 < 2 ^ B :=
        tailCount_step_lt n hn ⟨t, by omega⟩ st.1 hwle
      have hst2_lt : st.2 < 2 ^ B := by omega
      have hsum_eq : ∀ (x y : ℕ), x < 2 ^ B → y < 2 ^ B → x + y < 2 ^ B →
          (fun b : Fin B => addBFun B (Fin.append (natToBits B x) (natToBits B y)) b.castSucc) =
          natToBits B (x + y) := by
        intro x y hx hy hxy
        funext b
        unfold addBFun
        have hL : (fun i : Fin B => Fin.append (natToBits B x) (natToBits B y) ⟨i.val, by omega⟩) = natToBits B x := by
          funext i; change Fin.append _ _ (Fin.castAdd B i) = _; rw [Fin.append_left]
        have hR : (fun i : Fin B => Fin.append (natToBits B x) (natToBits B y) ⟨B + i.val, by omega⟩) = natToBits B y := by
          funext i
          have : (⟨B + i.val, by omega⟩ : Fin (B + B)) = Fin.natAdd B i := by apply Fin.ext; simp [Fin.natAdd]
          rw [this, Fin.append_right]
        rw [hL, hR, bitsToNat_natToBits hx, bitsToNat_natToBits hy]
        rfl
      cases hu : u ⟨t, by omega⟩
      · simp only [Bool.false_and, Bool.toNat_false, Nat.add_zero, Bool.false_eq_true, ↓reduceIte]
        have hz : (fun _ : Fin B => false) = natToBits B 0 := by funext b; simp [natToBits]
        rw [hz, hsum_eq st.2 0 hst2_lt (by positivity) (by omega)]
        simp only [Nat.add_zero]
      · simp only [Bool.true_and, Bool.toNat_true, ↓reduceIte]
        have hnext_lt : st.2 + tailCount n (n - 1 - t) st.1 < 2 ^ B := by
          rw [htake, List.foldl_append, List.foldl_cons, List.foldl_nil, ← hst] at hrank_next
          simp only [rankStep, hu, ↓reduceIte] at hrank_next
          omega
        rw [hsum_eq st.2 (tailCount n (n - 1 - t) st.1) hst2_lt hT_lt hnext_lt]
  have hn_inv := hinv n le_rfl
  have htake : (List.finRange n).take n = List.finRange n := by simp
  simp only [htake] at hn_inv
  unfold rankCircFun rankFold
  funext b
  rw [hn_inv, Fin.append_right]

lemma HasCirc.rankCirc (n : ℕ) (hn : 1 ≤ n) :
    let B := n - n / 384 + 2
    HasCirc n B (2 * (n + 1 + B) + n * (B * (n + 3) + 17 * B + 4 * (n + 1) + 2))
      (rankCircFun n B) := by
  intro B
  have hB : 0 < B := by omega
  have hinit : HasCirc n ((n + 1) + B) (2 * (n + 1 + B))
      (fun _ => Fin.append (oneHot n 0) (fun _ => false)) := by
    have h := HasCirc.vecConst (n := n) (m := (n + 1) + B) (B := 2)
      (f := fun _ => Fin.append (oneHot n 0) (fun _ => false))
      (fun j => HasCirc.const hn (Fin.append (oneHot n 0) (fun _ => false) j))
    simpa [Nat.mul_comm] using h
  have hfold := HasCirc.foldl hinit n (rankCircStepFun n B) (fun i => HasCirc.rankCircStep n B hB i)
  exact (HasCirc.comp hfold (HasCirc.proj (Fin.natAdd (n + 1)))).weaken (by omega)

def unrankCircStepFun (n B : ℕ) (i : Fin n) (inp : Fin (B + ((n + 1) + B + n)) → Bool) :
    Fin ((n + 1) + B + n) → Bool :=
  let oh : Fin (n + 1) → Bool := fun w => inp ⟨B + w.val, by omega⟩
  let rem : Fin B → Bool := fun b => inp ⟨B + (n + 1) + b.val, by omega⟩
  let out : Fin n → Bool := fun j => inp ⟨B + (n + 1) + B + j.val, by omega⟩
  let T := oneHotLookupFun n B (fun w => tailCount n (n - 1 - i.val) w.val) oh
  let sc := subCmpFun B (Fin.append rem T)
  let ge := sc (Fin.last B)
  let rem' : Fin B → Bool := fun b => if ge then sc b.castSucc else rem b
  let oh' := oneHotShiftFun n (Fin.append (fun _ : Fin 1 => ge) oh)
  let out' : Fin n → Bool := fun j => if j = i then ge else out j
  Fin.append (Fin.append oh' rem') out'

lemma HasCirc.unrankCircStep (n B : ℕ) (hB : 0 < B) (i : Fin n) :
    HasCirc (B + ((n + 1) + B + n)) ((n + 1) + B + n)
      (B * (n + 3) + 21 * B + 4 * (n + 1) + 2)
      (unrankCircStepFun n B i) := by
  set I := B + ((n + 1) + B + n)
  have hoh : HasCirc I (n + 1) 0 (fun inp w => inp ⟨B + w.val, by omega⟩) := HasCirc.proj _
  have hrem : HasCirc I B 0 (fun inp b => inp ⟨B + (n + 1) + b.val, by omega⟩) := HasCirc.proj _
  have hout : HasCirc I n 0 (fun inp j => inp ⟨B + (n + 1) + B + j.val, by omega⟩) := HasCirc.proj _
  have hT : HasCirc I B (B * (n + 3))
      (fun inp => oneHotLookupFun n B (fun w => tailCount n (n - 1 - i.val) w.val)
        (fun w => inp ⟨B + w.val, by omega⟩)) :=
    (HasCirc.comp hoh (HasCirc.oneHotLookup n B (fun w => tailCount n (n - 1 - i.val) w.val))).weaken (by omega)
  have hsc : HasCirc I (B + 1) (B * (n + 3) + 17 * B + 2)
      (fun inp => subCmpFun B (Fin.append (fun b => inp ⟨B + (n + 1) + b.val, by omega⟩)
        (oneHotLookupFun n B (fun w => tailCount n (n - 1 - i.val) w.val)
          (fun w => inp ⟨B + w.val, by omega⟩)))) :=
    (HasCirc.comp (HasCirc.pair hrem hT) (HasCirc.subCmp B hB)).weaken (by omega)
  have hstage1 := HasCirc.pair hsc (HasCirc.proj (n := I) (m := I) id)
  set S1 := (B + 1) + I
  have hge_s1 : HasCirc S1 1 0 (fun y _ => y ⟨B, by omega⟩) := HasCirc.proj _
  have hoh_s1 : HasCirc S1 (n + 1) 0 (fun y w => y ⟨(B + 1) + (B + w.val), by omega⟩) := HasCirc.proj _
  have hoh' : HasCirc S1 (n + 1) ((n + 1) * 4)
      (fun y => oneHotShiftFun n (Fin.append (fun _ : Fin 1 => y ⟨B, by omega⟩)
        (fun w => y ⟨(B + 1) + (B + w.val), by omega⟩))) :=
    (HasCirc.comp (HasCirc.pair hge_s1 hoh_s1) (HasCirc.oneHotShift n)).weaken (by omega)
  have hrem' : HasCirc S1 B (B * 4)
      (fun y b => if y ⟨B, by omega⟩ then y ⟨b.val, by omega⟩ else y ⟨(B + 1) + (B + (n + 1) + b.val), by omega⟩) :=
    HasCirc.vecConst (B := 4) (fun b =>
      (HasCirc.ite3 hge_s1 (HasCirc.proj (n := S1) (m := 1) (fun _ => ⟨b.val, by omega⟩))
        (HasCirc.proj (n := S1) (m := 1) (fun _ => ⟨(B + 1) + (B + (n + 1) + b.val), by omega⟩))).weaken (by omega))
  have hout' : HasCirc S1 n 0
      (fun y j => if j = i then y ⟨B, by omega⟩ else y ⟨(B + 1) + (B + (n + 1) + B + j.val), by omega⟩) :=
    (HasCirc.proj (n := S1) (m := n) (fun j =>
      if j = i then ⟨B, by omega⟩ else ⟨(B + 1) + (B + (n + 1) + B + j.val), by omega⟩)).congr
      (fun y j => by split_ifs <;> rfl)
  have hstage2 := HasCirc.pair (HasCirc.pair hoh' hrem') hout'
  refine (HasCirc.comp hstage1 hstage2).weaken (by omega) |>.congr ?_
  intro inp idx
  unfold unrankCircStepFun
  dsimp only
  simp only [id_eq]
  change Fin.append
      (Fin.append
        (oneHotShiftFun n
          (Fin.append (fun _ => Fin.append (subCmpFun B _) inp ⟨B, _⟩)
            (fun w => Fin.append (subCmpFun B _) inp ⟨(B + 1) + (B + w.val), _⟩)))
        (fun b =>
          if Fin.append (subCmpFun B _) inp ⟨B, _⟩ then Fin.append (subCmpFun B _) inp ⟨b.val, _⟩
          else Fin.append (subCmpFun B _) inp ⟨(B + 1) + (B + (n + 1) + b.val), _⟩))
      (fun j =>
        if j = i then Fin.append (subCmpFun B _) inp ⟨B, _⟩
        else Fin.append (subCmpFun B _) inp ⟨(B + 1) + (B + (n + 1) + B + j.val), _⟩)
      idx = _
  set sc := subCmpFun B (Fin.append (fun b : Fin B => inp ⟨B + (n + 1) + b.val, by omega⟩)
    (oneHotLookupFun n B (fun w => tailCount n (n - 1 - i.val) w.val)
      (fun w => inp ⟨B + w.val, by omega⟩)))
  have hsc_get : ∀ (k : Fin (B + 1)),
      Fin.append sc inp ⟨k.val, by omega⟩ = sc k := by
    intro k; change Fin.append sc inp (Fin.castAdd I k) = sc k; rw [Fin.append_left]
  have hinp_get : ∀ (k : Fin I),
      Fin.append sc inp ⟨(B + 1) + k.val, by omega⟩ = inp k := by
    intro k
    have : (⟨(B + 1) + k.val, by omega⟩ : Fin S1) = Fin.natAdd (B + 1) k := by
      apply Fin.ext; simp [Fin.natAdd]
    rw [this, Fin.append_right]
  have hge_eq : Fin.append sc inp ⟨B, by omega⟩ = sc (Fin.last B) := hsc_get (Fin.last B)
  have hoh_eq : (fun w : Fin (n + 1) => Fin.append sc inp ⟨(B + 1) + (B + w.val), by omega⟩) =
      fun w => inp ⟨B + w.val, by omega⟩ := funext fun w => hinp_get ⟨B + w.val, by omega⟩
  have hrem_eq : (fun b : Fin B =>
      if Fin.append sc inp ⟨B, by omega⟩ then Fin.append sc inp ⟨b.val, by omega⟩
      else Fin.append sc inp ⟨(B + 1) + (B + (n + 1) + b.val), by omega⟩) =
      fun b => if sc (Fin.last B) then sc b.castSucc else inp ⟨B + (n + 1) + b.val, by omega⟩ := by
    funext b
    have hsb : Fin.append sc inp ⟨b.val, by omega⟩ = sc b.castSucc := hsc_get b.castSucc
    rw [hge_eq, hsb, hinp_get ⟨B + (n + 1) + b.val, by omega⟩]
  have hout_eq : (fun j : Fin n =>
      if j = i then Fin.append sc inp ⟨B, by omega⟩
      else Fin.append sc inp ⟨(B + 1) + (B + (n + 1) + B + j.val), by omega⟩) =
      fun j => if j = i then sc (Fin.last B) else inp ⟨B + (n + 1) + B + j.val, by omega⟩ := by
    funext j
    split_ifs
    · exact hge_eq
    · exact hinp_get ⟨B + (n + 1) + B + j.val, by omega⟩
  rw [hrem_eq, hout_eq, hge_eq, hoh_eq]

def unrankCircFun (n B : ℕ) (rBits : Fin B → Bool) : Fin n → Bool :=
  let init : Fin ((n + 1) + B + n) → Bool :=
    Fin.append (Fin.append (oneHot n 0) rBits) (fun _ => false)
  let final := (List.finRange n).foldl (fun st i => unrankCircStepFun n B i (Fin.append rBits st)) init
  fun j => final (Fin.natAdd ((n + 1) + B) j)

lemma unrankCircFun_eq (n : ℕ) (hn : 1 ≤ n) (r : ℕ)
    (hr : r < 2 ^ (n - n / 384 + 2)) :
    let B := n - n / 384 + 2
    unrankCircFun n B (natToBits B r) = unrankFold n r := by
  intro B
  let rBits := natToBits B r
  let init : Fin ((n + 1) + B + n) → Bool :=
    Fin.append (Fin.append (oneHot n 0) rBits) (fun _ => false)
  have hinv : ∀ t ≤ n,
      let st := ((List.finRange n).take t).foldl (unrankStep n) (0, r, fun _ => false)
      st.1 ≤ t ∧ st.2.1 < 2 ^ B ∧
      ((List.finRange n).take t).foldl (fun s i => unrankCircStepFun n B i (Fin.append rBits s)) init =
        Fin.append (Fin.append (oneHot n st.1) (natToBits B st.2.1)) st.2.2 := by
    intro t ht
    induction t with
    | zero =>
      exact ⟨le_rfl, hr, rfl⟩
    | succ t ih =>
      rcases ih (by omega) with ⟨hwle, hrem_lt, ihs⟩
      set st := ((List.finRange n).take t).foldl (unrankStep n) (0, r, fun _ => false) with hst
      have htake := take_succ_finRange (n := n) (t := t) (by omega)
      dsimp only
      rw [htake, List.foldl_append, List.foldl_cons, List.foldl_nil,
        List.foldl_append, List.foldl_cons, List.foldl_nil, ← hst, ihs]
      unfold unrankCircStepFun unrankStep
      dsimp only
      set s_cur := Fin.append (Fin.append (oneHot n st.1) (natToBits B st.2.1)) st.2.2
      have hoh : (fun w : Fin (n + 1) => Fin.append rBits s_cur ⟨B + w.val, by omega⟩) = oneHot n st.1 := by
        funext w
        have : (⟨B + w.val, by omega⟩ : Fin (B + ((n + 1) + B + n))) =
            Fin.natAdd B (Fin.castAdd n (Fin.castAdd B w)) := by apply Fin.ext; simp [Fin.natAdd]
        rw [this, Fin.append_right]
        dsimp [s_cur]
        rw [Fin.append_left, Fin.append_left]
      have hrem_pt : ∀ b : Fin B, Fin.append rBits s_cur ⟨B + (n + 1) + b.val, by omega⟩ = natToBits B st.2.1 b := by
        intro b
        have : (⟨B + (n + 1) + b.val, by omega⟩ : Fin (B + ((n + 1) + B + n))) =
            Fin.natAdd B (Fin.castAdd n (Fin.natAdd (n + 1) b)) := by apply Fin.ext; simp [Fin.natAdd]; omega
        rw [this, Fin.append_right]
        dsimp [s_cur]
        rw [Fin.append_left, Fin.append_right]
      have hrem : (fun b : Fin B => Fin.append rBits s_cur ⟨B + (n + 1) + b.val, by omega⟩) = natToBits B st.2.1 :=
        funext hrem_pt
      have hout_pt : ∀ j : Fin n, Fin.append rBits s_cur ⟨B + (n + 1) + B + j.val, by omega⟩ = st.2.2 j := by
        intro j
        have : (⟨B + (n + 1) + B + j.val, by omega⟩ : Fin (B + ((n + 1) + B + n))) =
            Fin.natAdd B (Fin.natAdd ((n + 1) + B) j) := by apply Fin.ext; simp [Fin.natAdd]; omega
        rw [this, Fin.append_right]
        dsimp [s_cur]
        rw [Fin.append_right]
      simp only [hoh, hrem, hrem_pt, hout_pt]
      rw [oneHotLookup_spec n B _ st.1 (by omega)]
      set T := tailCount n (n - 1 - t) st.1
      have hT_lt : T < 2 ^ B := tailCount_step_lt n hn ⟨t, by omega⟩ st.1 hwle
      have hL : (fun i : Fin B => Fin.append (natToBits B st.2.1) (natToBits B T) ⟨i.val, by omega⟩) =
          natToBits B st.2.1 := by
        funext i; change Fin.append _ _ (Fin.castAdd B i) = _; rw [Fin.append_left]
      have hR : (fun i : Fin B => Fin.append (natToBits B st.2.1) (natToBits B T) ⟨B + i.val, by omega⟩) =
          natToBits B T := by
        funext i
        have : (⟨B + i.val, by omega⟩ : Fin (B + B)) = Fin.natAdd B i := by apply Fin.ext; simp [Fin.natAdd]
        rw [this, Fin.append_right]
      have htop : subCmpFun B (Fin.append (natToBits B st.2.1) (natToBits B T)) (Fin.last B) =
          decide (T ≤ st.2.1) := by
        rw [subCmpFun_top, hL, hR, bitsToNat_natToBits hrem_lt, bitsToNat_natToBits hT_lt]
      rw [htop]
      by_cases hle : T ≤ st.2.1
      · simp only [hle, decide_true, ↓reduceIte]
        have hlow : (fun b : Fin B => subCmpFun B (Fin.append (natToBits B st.2.1) (natToBits B T)) b.castSucc) =
            natToBits B (st.2.1 - T) := by
          apply bitsToNat_inj
          rw [subCmpFun_low _ (by rw [hL, hR, bitsToNat_natToBits hrem_lt, bitsToNat_natToBits hT_lt]; exact hle)]
          rw [hL, hR, bitsToNat_natToBits hrem_lt, bitsToNat_natToBits hT_lt, bitsToNat_natToBits (by omega)]
        rw [hlow, oneHotShift_spec n st.1 (by omega) true]
        exact ⟨by omega, by omega, rfl⟩
      · simp only [hle, decide_false, Bool.false_eq_true, ↓reduceIte]
        rw [oneHotShift_spec n st.1 (by omega) false]
        exact ⟨by omega, hrem_lt, rfl⟩
  have hn_inv := (hinv n le_rfl).2.2
  have htake : (List.finRange n).take n = List.finRange n := by simp
  simp only [htake] at hn_inv
  unfold unrankCircFun unrankFold
  funext j
  rw [hn_inv, Fin.append_right]

lemma HasCirc.unrankCirc (n : ℕ) (hn : 1 ≤ n) :
    let B := n - n / 384 + 2
    HasCirc B n (2 * (n + 1 + n) + n * (B * (n + 3) + 21 * B + 4 * (n + 1) + 2))
      (unrankCircFun n B) := by
  intro B
  have hB : 0 < B := by omega
  have hinit_oh : HasCirc B (n + 1) (2 * (n + 1)) (fun _ => oneHot n 0) := by
    have h := HasCirc.vecConst (n := B) (m := n + 1) (B := 2) (f := fun _ => oneHot n 0)
      (fun j => HasCirc.const hB (oneHot n 0 j))
    simpa [Nat.mul_comm] using h
  have hinit_rem : HasCirc B B 0 (fun r => r) := HasCirc.proj id
  have hinit_out : HasCirc B n (2 * n) (fun _ _ => false) := by
    have h := HasCirc.vecConst (n := B) (m := n) (B := 2) (f := fun _ _ => false)
      (fun _ => HasCirc.const hB false)
    simpa [Nat.mul_comm] using h
  have hinit : HasCirc B ((n + 1) + B + n) (2 * (n + 1 + n))
      (fun r => Fin.append (Fin.append (oneHot n 0) r) (fun _ => false)) :=
    (HasCirc.pair (HasCirc.pair hinit_oh hinit_rem) hinit_out).weaken (by omega)
  have hfold := HasCirc.foldl hinit n (unrankCircStepFun n B) (fun i => HasCirc.unrankCircStep n B hB i)
  exact (HasCirc.comp hfold (HasCirc.proj (Fin.natAdd ((n + 1) + B)))).weaken (by omega)

lemma list_eq_ofFn {m : ℕ} (l : List Bool) (f : Fin m → Bool)
    (hlen : l.length = m) (hget : ∀ i : Fin m, l.getD i.val false = f i) :
    l = List.ofFn f := by
  apply List.ext_getElem (by simp [hlen])
  intro i h1 h2
  have h3 := hget ⟨i, by omega⟩
  rw [List.getD_eq_getElem l false h1] at h3
  simpa using h3

lemma poly_bound (k : ℕ) (hk : 4096 ≤ k) :
    1000000 * (k + 1) ^ 3 ≤ (k + 1) ^ 200 := by
  have hsq : 1000000 ≤ (k + 1) ^ 2 := by nlinarith
  have h1 : 1000000 * (k + 1) ^ 3 ≤ (k + 1) ^ 2 * (k + 1) ^ 3 :=
    Nat.mul_le_mul_right _ hsq
  have h2 : (k + 1) ^ 2 * (k + 1) ^ 3 = (k + 1) ^ 5 := by rw [← pow_add]
  have h3 : (k + 1) ^ 5 ≤ (k + 1) ^ 200 := Nat.pow_le_pow_right (by omega) (by omega)
  omega

def xPref {k : ℕ} (hk : 1 ≤ k) (w : (Fin k → Bool) × (Fin (k - 1) → Bool)) : Fin (k - 1) → Bool :=
  fun j => w.1 ⟨j.val, by omega⟩

def uVec {k : ℕ} (hk : 1 ≤ k) (w : (Fin k → Bool) × (Fin (k - 1) → Bool)) : Fin (k - 1) → Bool :=
  fun j => Bool.xor (xPref hk w j) (w.2 j)

def flagBit {k : ℕ} (hk : 1 ≤ k) (w : (Fin k → Bool) × (Fin (k - 1) → Bool)) : Bool :=
  decide (16 * Nat.dist (2 * popcountVal (uVec hk w)) (k - 1) ≤ k - 1)

lemma flagBit_eq {k : ℕ} (hk : 1 ≤ k) (w : (Fin k → Bool) × (Fin (k - 1) → Bool)) :
    flagBit hk w =
      decide (16 * Nat.dist (2 * (Finset.univ.filter (fun j : Fin (k - 1) =>
        (List.ofFn w.1).getD j.val false ≠ w.2 j)).card) (k - 1) ≤ k - 1) := by
  have hcard : popcountVal (uVec hk w) =
      (Finset.univ.filter (fun j : Fin (k - 1) => (List.ofFn w.1).getD j.val false ≠ w.2 j)).card := by
    rw [popcountVal_eq_card]
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, uVec, xPref]
    have hget : (List.ofFn w.1).getD j.val false = w.1 ⟨j.val, by omega⟩ := by
      rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn]
    rw [hget]
    cases h1 : w.1 ⟨j.val, by omega⟩ <;> cases h2 : w.2 j <;> simp [h1, h2]
  unfold flagBit
  rw [hcard]

def tagTrueFun (k : ℕ) (hk : 4096 ≤ k)
    (H : Fin ((3 * (k - 1) + 7) / 8) → Fin (k - 1) → Bool)
    (inp : Fin (k + (k - 1)) → Bool) : Fin (2 * k - k / 1024) → Bool :=
  let n := k - 1
  let q := (n + 4) / 5
  let r := (3 * n + 7) / 8
  let xp : Fin n → Bool := fun j => inp ⟨j.val, by omega⟩
  let zp : Fin n → Bool := fun j => inp ⟨k + j.val, by omega⟩
  let packed := packAllTrits n xp zp
  let syn := syndrome H xp
  fun j =>
    if j.val = 0 then true
    else if j.val = 1 then inp ⟨n, by omega⟩
    else if h1 : j.val < 2 + q * 8 then packed ⟨j.val - 2, by omega⟩
    else if h2 : j.val < 2 + q * 8 + r then syn ⟨j.val - (2 + q * 8), by omega⟩
    else false

def tagFalseFun (k : ℕ) (hk : 4096 ≤ k)
    (inp : Fin (k + (k - 1)) → Bool) : Fin (2 * k - k / 1024) → Bool :=
  let n := k - 1
  let B := n - n / 384 + 2
  let uv : Fin n → Bool := fun j => Bool.xor (inp ⟨j.val, by omega⟩) (inp ⟨k + j.val, by omega⟩)
  let rk := rankCircFun n B uv
  fun j =>
    if j.val = 0 then false
    else if h1 : j.val < 1 + k then inp ⟨j.val - 1, by omega⟩
    else if h2 : j.val < 1 + k + B then rk ⟨j.val - (1 + k), by omega⟩
    else false

def tagCircFun (k : ℕ) (hk : 4096 ≤ k)
    (H : Fin ((3 * (k - 1) + 7) / 8) → Fin (k - 1) → Bool)
    (inp : Fin (k + (k - 1)) → Bool) : Fin (2 * k - k / 1024) → Bool :=
  let n := k - 1
  let d := popcountVal (fun j : Fin n => Bool.xor (inp ⟨j.val, by omega⟩) (inp ⟨k + j.val, by omega⟩))
  let fl := decide (16 * Nat.dist (2 * d) n ≤ n)
  fun j => if fl then tagTrueFun k hk H inp j else tagFalseFun k hk inp j

lemma HasCirc.tagTrueCirc (k : ℕ) (hk : 4096 ≤ k)
    (H : Fin ((3 * (k - 1) + 7) / 8) → Fin (k - 1) → Bool) :
    let n := k - 1
    let q := (n + 4) / 5
    let r := (3 * n + 7) / 8
    HasCirc (k + n) (2 * k - k / 1024) (q * 82000 + r * (4 * n + 2) + 4) (tagTrueFun k hk H) := by
  intro n q r
  set I := k + n
  have hI : 0 < I := by omega
  have hc1 : HasCirc I 1 2 (fun _ _ => true) := HasCirc.const hI true
  have hc0 : HasCirc I 1 2 (fun _ _ => false) := HasCirc.const hI false
  have hsp : HasCirc I 1 0 (fun inp _ => inp ⟨n, by omega⟩) := HasCirc.proj _
  have hpk := HasCirc.packAllTritsCirc k (by omega)
  have hxp : HasCirc I n 0 (fun inp j => inp ⟨j.val, by omega⟩) := HasCirc.proj _
  have hsyn : HasCirc I r (r * (4 * n + 2))
      (fun inp => syndrome H (fun j : Fin n => inp ⟨j.val, by omega⟩)) :=
    (HasCirc.comp hxp (HasCirc.syndromeCirc (by omega) H)).weaken (by dsimp only [n, r]; omega)
  have hp1 := HasCirc.pair hc1 hc0
  have hp2 := HasCirc.pair hp1 hsp
  have hp3 := HasCirc.pair hp2 hpk
  have hp4 := HasCirc.pair hp3 hsyn
  set S := (((1 + 1) + 1) + q * 8) + r
  let idx : Fin (2 * k - k / 1024) → Fin S := fun j =>
    if j.val = 0 then ⟨0, by omega⟩
    else if j.val = 1 then ⟨2, by omega⟩
    else if h1 : j.val < 2 + q * 8 then ⟨3 + (j.val - 2), by omega⟩
    else if h2 : j.val < 2 + q * 8 + r then ⟨3 + q * 8 + (j.val - (2 + q * 8)), by omega⟩
    else ⟨1, by omega⟩
  refine (HasCirc.comp hp4 (HasCirc.proj idx)).weaken (by dsimp only [n, q, r]; omega) |>.congr ?_
  intro inp j
  unfold tagTrueFun
  dsimp only [idx]
  split_ifs with h0 h1 h2 h3
  · change Fin.append _ _ (Fin.castAdd r (Fin.castAdd (q * 8) (Fin.castAdd 1 (Fin.castAdd 1 0)))) = true
    rw [Fin.append_left, Fin.append_left, Fin.append_left, Fin.append_left]
  · change Fin.append _ _ (Fin.castAdd r (Fin.castAdd (q * 8) (Fin.natAdd (1 + 1) 0))) = inp ⟨n, by omega⟩
    rw [Fin.append_left, Fin.append_left, Fin.append_right]
  · have hpos : (⟨3 + (j.val - 2), by omega⟩ : Fin S) =
        Fin.castAdd r (Fin.natAdd ((1 + 1) + 1) ⟨j.val - 2, by omega⟩) := by
      apply Fin.ext; simp [Fin.natAdd]
    rw [hpos, Fin.append_left, Fin.append_right]
  · have hpos : (⟨3 + q * 8 + (j.val - (2 + q * 8)), by omega⟩ : Fin S) =
        Fin.natAdd (((1 + 1) + 1) + q * 8) ⟨j.val - (2 + q * 8), by omega⟩ := by
      apply Fin.ext; simp [Fin.natAdd]
    rw [hpos, Fin.append_right]
  · change Fin.append _ _ (Fin.castAdd r (Fin.castAdd (q * 8) (Fin.castAdd 1 (Fin.natAdd 1 0)))) = false
    rw [Fin.append_left, Fin.append_left, Fin.append_left, Fin.append_right]

lemma HasCirc.tagFalseCirc (k : ℕ) (hk : 4096 ≤ k) :
    let n := k - 1
    let B := n - n / 384 + 2
    HasCirc (k + n) (2 * k - k / 1024)
      (4 * n + 2 * (n + 1 + B) + n * (B * (n + 3) + 17 * B + 4 * (n + 1) + 2) + 2)
      (tagFalseFun k hk) := by
  intro n B
  set I := k + n
  have hI : 0 < I := by omega
  have hn : 1 ≤ n := by omega
  have hc0 : HasCirc I 1 2 (fun _ _ => false) := HasCirc.const hI false
  have hx : HasCirc I k 0 (fun inp j => inp ⟨j.val, by omega⟩) := HasCirc.proj _
  have huv : HasCirc I n (4 * n)
      (fun inp j => Bool.xor (inp ⟨j.val, by omega⟩) (inp ⟨k + j.val, by omega⟩)) := by
    have h := HasCirc.vecConst (n := I) (m := n) (B := 4)
      (fun j => HasCirc.xor2
        (HasCirc.proj (n := I) (m := 1) (fun _ => ⟨j.val, by omega⟩))
        (HasCirc.proj (n := I) (m := 1) (fun _ => ⟨k + j.val, by omega⟩)))
    simpa [Nat.mul_comm] using h
  have hrk := HasCirc.comp huv (HasCirc.rankCirc n hn)
  have hp := HasCirc.pair (HasCirc.pair hc0 hx) hrk
  set S := (1 + k) + B
  let idx : Fin (2 * k - k / 1024) → Fin S := fun j =>
    if j.val = 0 then ⟨0, by omega⟩
    else if h1 : j.val < 1 + k then ⟨1 + (j.val - 1), by omega⟩
    else if h2 : j.val < 1 + k + B then ⟨(1 + k) + (j.val - (1 + k)), by omega⟩
    else ⟨0, by omega⟩
  refine (HasCirc.comp hp (HasCirc.proj idx)).weaken (by dsimp only [n, B]; omega) |>.congr ?_
  intro inp j
  unfold tagFalseFun
  dsimp only [idx]
  split_ifs with h0 h1 h2
  · change Fin.append _ _ (Fin.castAdd B (Fin.castAdd k 0)) = false
    rw [Fin.append_left, Fin.append_left]
  · have hpos : (⟨1 + (j.val - 1), by omega⟩ : Fin S) =
        Fin.castAdd B (Fin.natAdd 1 ⟨j.val - 1, by omega⟩) := by
      apply Fin.ext; simp [Fin.natAdd]
    rw [hpos, Fin.append_left, Fin.append_right]
  · have hpos : (⟨(1 + k) + (j.val - (1 + k)), by omega⟩ : Fin S) =
        Fin.natAdd (1 + k) ⟨j.val - (1 + k), by omega⟩ := by
      apply Fin.ext; simp [Fin.natAdd]
    rw [hpos, Fin.append_right]
  · change Fin.append _ _ (Fin.castAdd B (Fin.castAdd k 0)) = false
    rw [Fin.append_left, Fin.append_left]

lemma HasCirc.tagCirc (k : ℕ) (hk : 4096 ≤ k)
    (H : Fin ((3 * (k - 1) + 7) / 8) → Fin (k - 1) → Bool) :
    HasCirc (k + (k - 1)) (2 * k - k / 1024) ((k + 1) ^ 200) (tagCircFun k hk H) := by
  let n := k - 1
  let c := 2 * k - k / 1024
  let q := (n + 4) / 5
  let r := (3 * n + 7) / 8
  let B := n - n / 384 + 2
  have hfl := HasCirc.flagCirc k (by omega)
  have hT := HasCirc.tagTrueCirc k hk H
  have hF := HasCirc.tagFalseCirc k hk
  have hp := HasCirc.pair (HasCirc.pair hfl hT) hF
  set S := (1 + c) + c
  have hmux : HasCirc S c (c * 4)
      (fun y j => if y ⟨0, by omega⟩ then y ⟨1 + j.val, by omega⟩ else y ⟨(1 + c) + j.val, by omega⟩) :=
    HasCirc.vecConst (B := 4) (fun j =>
      (HasCirc.ite3 (HasCirc.proj (n := S) (m := 1) (fun _ => ⟨0, by omega⟩))
        (HasCirc.proj (n := S) (m := 1) (fun _ => ⟨1 + j.val, by omega⟩))
        (HasCirc.proj (n := S) (m := 1) (fun _ => ⟨(1 + c) + j.val, by omega⟩))).weaken (by omega))
  have hbd :
      200 * (k + 1) + (q * 82000 + r * (4 * n + 2) + 4) +
        (4 * n + 2 * (n + 1 + B) + n * (B * (n + 3) + 17 * B + 4 * (n + 1) + 2) + 2) +
        c * 4 ≤ (k + 1) ^ 200 := by
    have hpoly := poly_bound k hk
    have hq : q ≤ k := by omega
    have hr : r ≤ k := by omega
    have hB : B ≤ k + 1 := by omega
    have hc : c ≤ 2 * k := by omega
    have hn : n ≤ k := by omega
    have hstep1 : B * (n + 3) + 17 * B + 4 * (n + 1) + 2 ≤ 30 * (k + 1) ^ 2 := by nlinarith
    have hstep2 : n * (B * (n + 3) + 17 * B + 4 * (n + 1) + 2) ≤ 30 * (k + 1) ^ 3 := by
      have : n * (B * (n + 3) + 17 * B + 4 * (n + 1) + 2) ≤ (k + 1) * (30 * (k + 1) ^ 2) :=
        Nat.mul_le_mul (by omega) hstep1
      nlinarith
    have hstep3 : r * (4 * n + 2) ≤ 6 * (k + 1) ^ 2 := by nlinarith
    have hstep4 : q * 82000 ≤ 82000 * (k + 1) := by omega
    have htot :
        200 * (k + 1) + (q * 82000 + r * (4 * n + 2) + 4) +
          (4 * n + 2 * (n + 1 + B) + n * (B * (n + 3) + 17 * B + 4 * (n + 1) + 2) + 2) +
          c * 4 ≤ 1000000 * (k + 1) ^ 3 := by nlinarith
    exact le_trans htot hpoly
  refine (HasCirc.comp hp hmux).weaken hbd |>.congr ?_
  intro inp j
  unfold tagCircFun
  dsimp only
  have h0 : Fin.append (Fin.append (fun _ : Fin 1 =>
      decide (16 * Nat.dist (2 * popcountVal fun j : Fin n => Bool.xor (inp ⟨j.val, by omega⟩) (inp ⟨k + j.val, by omega⟩)) n ≤ n))
      (tagTrueFun k hk H inp)) (tagFalseFun k hk inp) ⟨0, by omega⟩ =
      decide (16 * Nat.dist (2 * popcountVal fun j : Fin n => Bool.xor (inp ⟨j.val, by omega⟩) (inp ⟨k + j.val, by omega⟩)) n ≤ n) := by
    change Fin.append _ _ (Fin.castAdd c (Fin.castAdd c 0)) = _
    rw [Fin.append_left, Fin.append_left]
  have h1 : Fin.append (Fin.append (fun _ : Fin 1 =>
      decide (16 * Nat.dist (2 * popcountVal fun j : Fin n => Bool.xor (inp ⟨j.val, by omega⟩) (inp ⟨k + j.val, by omega⟩)) n ≤ n))
      (tagTrueFun k hk H inp)) (tagFalseFun k hk inp) ⟨1 + j.val, by omega⟩ = tagTrueFun k hk H inp j := by
    have : (⟨1 + j.val, by omega⟩ : Fin S) = Fin.castAdd c (Fin.natAdd 1 j) := by
      apply Fin.ext; simp [Fin.natAdd]
    rw [this, Fin.append_left, Fin.append_right]
  have h2 : Fin.append (Fin.append (fun _ : Fin 1 =>
      decide (16 * Nat.dist (2 * popcountVal fun j : Fin n => Bool.xor (inp ⟨j.val, by omega⟩) (inp ⟨k + j.val, by omega⟩)) n ≤ n))
      (tagTrueFun k hk H inp)) (tagFalseFun k hk inp) ⟨(1 + c) + j.val, by omega⟩ = tagFalseFun k hk inp j := by
    have : (⟨(1 + c) + j.val, by omega⟩ : Fin S) = Fin.natAdd (1 + c) j := by
      apply Fin.ext; simp [Fin.natAdd]
    rw [this, Fin.append_right]
  rw [h0, h1, h2]

lemma HasCirc.dec1Circ (k : ℕ) (hk : 4096 ≤ k) :
    let n := k - 1
    let c := 2 * k - k / 1024
    let q := (n + 4) / 5
    HasCirc (k + c) (k + n) ((k + 1) ^ 200) (fun inp =>
      let z : Fin n → Bool := fun j => inp ⟨j.val, by omega⟩
      let tg : Fin c → Bool := fun j => inp ⟨k + j.val, by omega⟩
      let xT_pref := unpackPartner n (fun i : Fin (q * 8) => tg ⟨2 + i.val, by omega⟩) z
      let xT : Fin k → Bool := fun j => if h : j.val < n then xT_pref ⟨j.val, h⟩ else tg ⟨1, by omega⟩
      let xF : Fin k → Bool := fun j => tg ⟨1 + j.val, by omega⟩
      let xRec : Fin k → Bool := fun j => if tg ⟨0, by omega⟩ then xT j else xF j
      Fin.append xRec z) := by
  intro n c q
  set I := k + c
  have hpk_z : HasCirc I (q * 8 + n) 0 (fun inp i =>
      if h : i.val < q * 8 then inp ⟨k + (2 + i.val), by omega⟩
      else inp ⟨i.val - q * 8, by omega⟩) :=
    (HasCirc.proj (n := I) (m := q * 8 + n) (fun i =>
      if h : i.val < q * 8 then ⟨k + (2 + i.val), by omega⟩
      else ⟨i.val - q * 8, by omega⟩)).congr (fun inp i => by split_ifs <;> rfl)
  have hunp := HasCirc.comp hpk_z (HasCirc.unpackPartnerCirc n)
  have hstage1 := HasCirc.pair hunp (HasCirc.proj (n := I) (m := I) id)
  set S := n + I
  have hxRec : HasCirc S k (k * 4) (fun st j =>
      if st ⟨n + k, by omega⟩ then
        (if h : j.val < n then st ⟨j.val, by omega⟩ else st ⟨n + (k + 1), by omega⟩)
      else st ⟨n + (k + (1 + j.val)), by omega⟩) := by
    apply HasCirc.vecConst (B := 4)
    intro j
    have hsel : HasCirc S 1 0 (fun st _ => st ⟨n + k, by omega⟩) := HasCirc.proj _
    have hF : HasCirc S 1 0 (fun st _ => st ⟨n + (k + (1 + j.val)), by omega⟩) := HasCirc.proj _
    by_cases hj : j.val < n
    · have hT : HasCirc S 1 0 (fun st _ => st ⟨j.val, by omega⟩) := HasCirc.proj _
      refine (HasCirc.ite3 hsel hT hF).weaken (by omega) |>.congr ?_
      intro st _; simp [hj]
    · have hT : HasCirc S 1 0 (fun st _ => st ⟨n + (k + 1), by omega⟩) := HasCirc.proj _
      refine (HasCirc.ite3 hsel hT hF).weaken (by omega) |>.congr ?_
      intro st _; simp [hj]
  have hz : HasCirc S n 0 (fun st j => st ⟨n + j.val, by omega⟩) := HasCirc.proj _
  have hstage2 := HasCirc.pair hxRec hz
  have hbd : 0 + (q * 25600 + 3 * n) + 0 + (k * 4 + 0) ≤ (k + 1) ^ 200 := by
    have hpoly := poly_bound k hk
    have hq : q ≤ k := by omega
    have hn : n ≤ k := by omega
    have hcube : k + 1 ≤ (k + 1) ^ 3 := le_self_pow₀ (by omega) (by omega)
    have htot : 0 + (q * 25600 + 3 * n) + 0 + (k * 4 + 0) ≤ 1000000 * (k + 1) ^ 3 := by omega
    exact le_trans htot hpoly
  refine (HasCirc.comp hstage1 hstage2).weaken hbd |>.congr ?_
  intro inp idx
  dsimp only
  simp only [id_eq]
  set xTp := unpackPartner n (fun i : Fin (q * 8) => inp ⟨k + (2 + i.val), by omega⟩)
    (fun j : Fin n => inp ⟨j.val, by omega⟩)
  have hleft : ∀ i : Fin n, Fin.append xTp inp ⟨i.val, by omega⟩ = xTp i := by
    intro i; change Fin.append xTp inp (Fin.castAdd I i) = xTp i; rw [Fin.append_left]
  have hright : ∀ i : Fin I, Fin.append xTp inp ⟨n + i.val, by omega⟩ = inp i := by
    intro i
    have : (⟨n + i.val, by omega⟩ : Fin S) = Fin.natAdd n i := by apply Fin.ext; simp [Fin.natAdd]
    rw [this, Fin.append_right]
  have hpk_eq : unpackPartner n
      (fun i : Fin (q * 8) => (if h : i.val < q * 8 then inp ⟨k + (2 + i.val), by omega⟩ else inp ⟨i.val - q * 8, by omega⟩))
      (fun j : Fin n => (if h : q * 8 + j.val < q * 8 then inp ⟨k + (2 + (q * 8 + j.val)), by omega⟩ else inp ⟨q * 8 + j.val - q * 8, by omega⟩)) = xTp := by
    congr 1
    · funext i; simp [i.isLt]
    · funext j
      have hge : ¬ (q * 8 + j.val < q * 8) := by omega
      simp [hge]
  rw [hpk_eq]
  congr 1
  · funext j
    have h0 : Fin.append xTp inp ⟨n + k, by omega⟩ = inp ⟨k + 0, by omega⟩ := by
      simpa using hright ⟨k, by omega⟩
    rw [h0, hright ⟨k + 1, by omega⟩, hright ⟨k + (1 + j.val), by omega⟩]
    split_ifs with hsel hj
    · exact hleft ⟨j.val, hj⟩
    · rfl
    · rfl
  · funext j
    exact hright ⟨j.val, by omega⟩

lemma HasCirc.dec2Circ (k : ℕ) (hk : 4096 ≤ k) :
    let n := k - 1
    let c := 2 * k - k / 1024
    let q := (n + 4) / 5
    let B := n - n / 384 + 2
    HasCirc (c + k) (k + n) ((k + 1) ^ 200) (fun inp =>
      let tg : Fin c → Bool := fun j => inp ⟨j.val, by omega⟩
      let x : Fin k → Bool := fun j => inp ⟨c + j.val, by omega⟩
      let xPrefV : Fin n → Bool := fun j => x ⟨j.val, by omega⟩
      let zT := unpackPartner n (fun i : Fin (q * 8) => tg ⟨2 + i.val, by omega⟩) xPrefV
      let uRec := unrankCircFun n B (fun b : Fin B => tg ⟨1 + k + b.val, by omega⟩)
      let zF : Fin n → Bool := fun j => Bool.xor (xPrefV j) (uRec j)
      let zRec : Fin n → Bool := fun j => if tg ⟨0, by omega⟩ then zT j else zF j
      Fin.append x zRec) := by
  intro n c q B
  set I := c + k
  have hn : 1 ≤ n := by omega
  have hpk_x : HasCirc I (q * 8 + n) 0 (fun inp i =>
      if h : i.val < q * 8 then inp ⟨2 + i.val, by omega⟩
      else inp ⟨c + (i.val - q * 8), by omega⟩) :=
    (HasCirc.proj (n := I) (m := q * 8 + n) (fun i =>
      if h : i.val < q * 8 then ⟨2 + i.val, by omega⟩
      else ⟨c + (i.val - q * 8), by omega⟩)).congr (fun inp i => by split_ifs <;> rfl)
  have hzT := HasCirc.comp hpk_x (HasCirc.unpackPartnerCirc n)
  have hrkIn : HasCirc I B 0 (fun inp b => inp ⟨1 + k + b.val, by omega⟩) := HasCirc.proj _
  have huRec := HasCirc.comp hrkIn (HasCirc.unrankCirc n hn)
  have hstage1 := HasCirc.pair (HasCirc.pair hzT huRec) (HasCirc.proj (n := I) (m := I) id)
  set S := (n + n) + I
  have hx : HasCirc S k 0 (fun st j => st ⟨(n + n) + (c + j.val), by omega⟩) := HasCirc.proj _
  have hzRec : HasCirc S n (n * 8) (fun st j =>
      if st ⟨(n + n) + 0, by omega⟩ then st ⟨j.val, by omega⟩
      else Bool.xor (st ⟨(n + n) + (c + j.val), by omega⟩) (st ⟨n + j.val, by omega⟩)) :=
    HasCirc.vecConst (B := 8) (fun j =>
      (HasCirc.ite3
        (HasCirc.proj (n := S) (m := 1) (fun _ => ⟨(n + n) + 0, by omega⟩))
        (HasCirc.proj (n := S) (m := 1) (fun _ => ⟨j.val, by omega⟩))
        (HasCirc.xor2
          (HasCirc.proj (n := S) (m := 1) (fun _ => ⟨(n + n) + (c + j.val), by omega⟩))
          (HasCirc.proj (n := S) (m := 1) (fun _ => ⟨n + j.val, by omega⟩)))).weaken (by omega))
  have hstage2 := HasCirc.pair hx hzRec
  have hbd :
      (0 + (q * 25600 + 3 * n) + (0 + (2 * (n + 1 + n) + n * (B * (n + 3) + 21 * B + 4 * (n + 1) + 2))) + 0) +
        (0 + n * 8) ≤ (k + 1) ^ 200 := by
    have hpoly := poly_bound k hk
    have hq : q ≤ k := by omega
    have hB : B ≤ k + 1 := by omega
    have hn_le : n ≤ k := by omega
    have hstep1 : B * (n + 3) + 21 * B + 4 * (n + 1) + 2 ≤ 40 * (k + 1) ^ 2 := by nlinarith
    have hstep2 : n * (B * (n + 3) + 21 * B + 4 * (n + 1) + 2) ≤ 40 * (k + 1) ^ 3 := by
      have : n * (B * (n + 3) + 21 * B + 4 * (n + 1) + 2) ≤ (k + 1) * (40 * (k + 1) ^ 2) :=
        Nat.mul_le_mul (by omega) hstep1
      nlinarith
    have htot :
        (0 + (q * 25600 + 3 * n) + (0 + (2 * (n + 1 + n) + n * (B * (n + 3) + 21 * B + 4 * (n + 1) + 2))) + 0) +
          (0 + n * 8) ≤ 1000000 * (k + 1) ^ 3 := by nlinarith
    exact le_trans htot hpoly
  refine (HasCirc.comp hstage1 hstage2).weaken hbd |>.congr ?_
  intro inp idx
  dsimp only
  simp only [id_eq]
  set zTv := unpackPartner n (fun i : Fin (q * 8) => inp ⟨2 + i.val, by omega⟩)
    (fun j : Fin n => inp ⟨c + j.val, by omega⟩)
  set uRv := unrankCircFun n B (fun b : Fin B => inp ⟨1 + k + b.val, by omega⟩)
  have hzT_eq : unpackPartner n
      (fun i : Fin (q * 8) => if h : i.val < q * 8 then inp ⟨2 + i.val, by omega⟩ else inp ⟨c + (i.val - q * 8), by omega⟩)
      (fun j : Fin n => if h : q * 8 + j.val < q * 8 then inp ⟨2 + (q * 8 + j.val), by omega⟩ else inp ⟨c + (q * 8 + j.val - q * 8), by omega⟩) = zTv := by
    congr 1
    · funext i; simp [i.isLt]
    · funext j
      have hge : ¬ (q * 8 + j.val < q * 8) := by omega
      simp [hge]
  rw [hzT_eq]
  have h1 : ∀ j : Fin n, Fin.append (Fin.append zTv uRv) inp ⟨j.val, by omega⟩ = zTv j := by
    intro j; change Fin.append _ _ (Fin.castAdd I (Fin.castAdd n j)) = zTv j
    rw [Fin.append_left, Fin.append_left]
  have h2 : ∀ j : Fin n, Fin.append (Fin.append zTv uRv) inp ⟨n + j.val, by omega⟩ = uRv j := by
    intro j
    have : (⟨n + j.val, by omega⟩ : Fin S) = Fin.castAdd I (Fin.natAdd n j) := by
      apply Fin.ext; simp [Fin.natAdd]
    rw [this, Fin.append_left, Fin.append_right]
  have h3 : ∀ i : Fin I, Fin.append (Fin.append zTv uRv) inp ⟨(n + n) + i.val, by omega⟩ = inp i := by
    intro i
    have : (⟨(n + n) + i.val, by omega⟩ : Fin S) = Fin.natAdd (n + n) i := by
      apply Fin.ext; simp [Fin.natAdd]
    rw [this, Fin.append_right]
  congr 1
  · funext j; exact h3 ⟨c + j.val, by omega⟩
  · funext j
    rw [h3 ⟨0, by omega⟩, h1 j, h3 ⟨c + j.val, by omega⟩, h2 j]

end PEqualNP.Outside.L_pcx_282_aux

theorem PEqualNP.Outside.L_pcx_282 : (∃ A K : ℕ, 0 < A ∧ ∀ k : ℕ, K ≤ k →
  let h := 1
  let c := 2*k-k/1024
  let X := Fin k → Bool
  let Z := Fin (k-h) → Bool
  let Word := X × Z
  let raw := fun w : Word => List.ofFn w.1 ++ List.ofFn w.2
  let flag := fun (w : Word) (_ : Fin h) =>
    let d := (Finset.univ.filter (fun j : Fin (k-h) => (List.ofFn w.1).getD j.val false ≠ w.2 j)).card
    decide (16 * Nat.dist (2*d) (k-h) ≤ k-h)
  let valid := fun (inputs budget : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) =>
    PEqualNP.MetaComplexity.NestedCover.ReadsBack inputs C ∧ C.size ≤ budget ∧
    ∀ g ∈ C.gates, ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) ∨
      (g.op = .not ∧ g.inputs.length = 1)
  ∃ (tag : Word → Fin c → Bool) (enc : PEqualNP.CircuitLowerBounds.Circuit)
    (tw : Fin c → Fin (k+(k-h)+enc.size)) (cw : Fin h → Fin (k+(k-h)+enc.size)),
    valid (k+(k-h)) ((k+1)^A) enc ∧
    (∀ w : Word, (∀ j, (enc.wires (raw w)).getD (tw j).val false = tag w j) ∧
      ∀ j, (enc.wires (raw w)).getD (cw j).val false = flag w j) ∧
    (∀ a b t : Word, a.1 = b.1 → b.2 = t.2 → flag b = flag t → tag t = tag a → a = b ∧ b = t) ∧
    (∀ e : Fin 3,
      let port := fun (i : Fin 3) (w : Word) =>
        if i = 0 then List.ofFn w.1 else if i = 1 then List.ofFn w.2 ++ List.ofFn (flag w)
        else List.ofFn (tag w)
      let len := fun i : Fin 3 => if i = 2 then c else k
      let inputs := len e + len (e+1)
      ∃ (dec : PEqualNP.CircuitLowerBounds.Circuit) (dw : Fin (k+(k-h)) → Fin (inputs+dec.size)),
        valid inputs ((k+1)^A) dec ∧ ∀ (w : Word) (j : Fin (k+(k-h))),
          (dec.wires (port e w ++ port (e+1) w)).getD (dw j).val false = (raw w).getD j.val false) ∧
    ∃ (gate : PEqualNP.CircuitLowerBounds.Circuit) (bit : Fin (k+(k-h)+gate.size)),
      valid (k+(k-h)) (A*(k+1)) gate ∧ ∀ w : Word,
        (gate.wires (raw w)).getD bit.val false = flag w 0) := by
  open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.Outside.L_pcx_282_aux in
  refine ⟨200, 4096, by omega, ?_⟩
  intro k hk
  dsimp only
  let n := k - 1
  let c := 2 * k - k / 1024
  let q := (n + 4) / 5
  let r := (3 * n + 7) / 8
  let B := n - n / 384 + 2
  have hk1 : 1 ≤ k := by omega
  have hn : 1 ≤ n := by omega
  have h1_fit : 2 + q * 8 + r ≤ c := by omega
  have h2_fit : 1 + k + B ≤ c := by omega
  rcases gv_matrix_exists n hn with ⟨H, hH⟩
  let rawVec : (Fin k → Bool) × (Fin n → Bool) → Fin (k + n) → Bool := fun w => Fin.append w.1 w.2
  have hraw_eq : ∀ w : (Fin k → Bool) × (Fin n → Bool),
      List.ofFn w.1 ++ List.ofFn w.2 = List.ofFn (rawVec w) := by
    intro w
    apply list_eq_ofFn
    · simp
    · intro i
      by_cases hi : i.val < k
      · rw [getD_append_left _ _ _ _ (by simp [hi]), List.getD_eq_getElem _ _ (by simp [hi]),
          List.getElem_ofFn]
        change w.1 ⟨i.val, hi⟩ = Fin.append w.1 w.2 (Fin.castAdd n ⟨i.val, hi⟩)
        rw [Fin.append_left]
      · rw [getD_append_right _ _ _ _ (by simp; omega), List.length_ofFn,
          List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn]
        have hnat : i = Fin.natAdd k ⟨i.val - k, by omega⟩ := by
          apply Fin.ext; simp [Fin.natAdd]; omega
        conv_rhs => rw [hnat]
        exact (Fin.append_right w.1 w.2 ⟨i.val - k, by omega⟩).symm
  have hraw_get1 : ∀ (w : (Fin k → Bool) × (Fin n → Bool)) (j : Fin k),
      rawVec w ⟨j.val, by omega⟩ = w.1 j := by
    intro w j; change Fin.append w.1 w.2 (Fin.castAdd n j) = w.1 j; rw [Fin.append_left]
  have hraw_get2 : ∀ (w : (Fin k → Bool) × (Fin n → Bool)) (j : Fin n),
      rawVec w ⟨k + j.val, by omega⟩ = w.2 j := by
    intro w j
    have : (⟨k + j.val, by omega⟩ : Fin (k + n)) = Fin.natAdd k j := by apply Fin.ext; simp [Fin.natAdd]
    rw [this]; exact Fin.append_right w.1 w.2 j
  let tag : (Fin k → Bool) × (Fin n → Bool) → Fin c → Bool := fun w => tagCircFun k hk H (rawVec w)
  have htag0 : ∀ w, tag w ⟨0, by omega⟩ = flagBit hk1 w := by
    intro w
    change tagCircFun k hk H (rawVec w) ⟨0, by omega⟩ = flagBit hk1 w
    unfold tagCircFun tagTrueFun tagFalseFun flagBit uVec xPref
    have hu : (fun j : Fin n => Bool.xor (rawVec w ⟨j.val, by omega⟩) (rawVec w ⟨k + j.val, by omega⟩)) =
        fun j : Fin n => Bool.xor (w.1 ⟨j.val, by omega⟩) (w.2 j) := by
      funext j; rw [hraw_get1 w ⟨j.val, by omega⟩, hraw_get2 w j]
    rw [hu]
    cases decide (16 * Nat.dist (2 * popcountVal fun j : Fin n => Bool.xor (w.1 ⟨j.val, by omega⟩) (w.2 j)) n ≤ n) <;> simp
  rcases HasCirc.tagCirc k hk H with ⟨enc, tw, hrb_enc, hvg_enc, hsz_enc, hev_enc⟩
  let cw : Fin 1 → Fin (k + n + enc.size) := fun _ => tw ⟨0, by omega⟩
  refine ⟨tag, enc, tw, cw, ⟨hrb_enc, hsz_enc, hvg_enc⟩, ?_, ?_, ?_, ?_⟩
  ·
    intro w
    constructor
    · intro j
      rw [hraw_eq w]
      exact hev_enc (rawVec w) j
    · intro j
      rw [hraw_eq w]
      dsimp only [cw]
      rw [hev_enc (rawVec w) ⟨0, by omega⟩]
      change tag w ⟨0, by omega⟩ = _
      rw [htag0 w, flagBit_eq hk1 w]
  ·
    intro a b t hab hbt hfb htt
    have hfl_bt : flagBit hk1 b = flagBit hk1 t := by
      have := congrFun hfb ⟨0, by omega⟩
      rwa [← flagBit_eq hk1 b, ← flagBit_eq hk1 t] at this
    have hfl_ta : flagBit hk1 t = flagBit hk1 a := by
      have := congrFun htt ⟨0, by omega⟩
      rwa [htag0 t, htag0 a] at this
    have hu_raw : ∀ w : (Fin k → Bool) × (Fin n → Bool),
        (fun j : Fin n => Bool.xor (rawVec w ⟨j.val, by omega⟩) (rawVec w ⟨k + j.val, by omega⟩)) = uVec hk1 w := by
      intro w; funext j; unfold uVec xPref; rw [hraw_get1 w ⟨j.val, by omega⟩, hraw_get2 w j]
    cases hflb : flagBit hk1 b
    ·
      have hflt : flagBit hk1 t = false := hfl_bt.symm.trans hflb
      have hfla : flagBit hk1 a = false := hfl_ta.symm.trans hflt
      have htf_eq : ∀ j : Fin c, tagFalseFun k hk (rawVec t) j = tagFalseFun k hk (rawVec a) j := by
        intro j
        have hj := congrFun htt j
        change tagCircFun k hk H (rawVec t) j = tagCircFun k hk H (rawVec a) j at hj
        unfold tagCircFun at hj
        rw [hu_raw t, hu_raw a] at hj
        change (if flagBit hk1 t then tagTrueFun k hk H (rawVec t) j else tagFalseFun k hk (rawVec t) j) =
          (if flagBit hk1 a then tagTrueFun k hk H (rawVec a) j else tagFalseFun k hk (rawVec a) j) at hj
        simpa [hflt, hfla] using hj
      have hx_eq : t.1 = a.1 := by
        funext j
        have hj := htf_eq ⟨1 + j.val, by omega⟩
        unfold tagFalseFun at hj
        have hne0 : ¬ (1 + j.val = 0) := by omega
        have hlt1 : 1 + j.val < 1 + k := by omega
        simp only [hne0, ↓reduceIte, hlt1, ↓reduceDIte, Nat.add_sub_cancel_left] at hj
        rwa [hraw_get1 t j, hraw_get1 a j] at hj
      have hrk_eq : rankCircFun n B (uVec hk1 t) = rankCircFun n B (uVec hk1 a) := by
        funext j
        have hj := htf_eq ⟨1 + k + j.val, by omega⟩
        unfold tagFalseFun at hj
        have hne0 : ¬ (1 + k + j.val = 0) := by omega
        have hge1 : ¬ (1 + k + j.val < 1 + k) := by omega
        have hlt2 : 1 + k + j.val < 1 + k + (k - 1 - (k - 1) / 384 + 2) := by omega
        simp only [hne0, ↓reduceIte, hge1, hlt2, ↓reduceDIte, Nat.add_sub_cancel_left] at hj
        rwa [hu_raw t, hu_raw a] at hj
      have hrt : isRare n (popcountVal (uVec hk1 t)) = true := by
        unfold isRare; unfold flagBit at hflt; rw [hflt]; rfl
      have hra : isRare n (popcountVal (uVec hk1 a)) = true := by
        unfold isRare; unfold flagBit at hfla; rw [hfla]; rfl
      have hu_eq : uVec hk1 t = uVec hk1 a := by
        have h1 : unrankCircFun n B (rankCircFun n B (uVec hk1 t)) = uVec hk1 t := by
          rw [rankCircFun_eq n hn (uVec hk1 t) hrt,
            unrankCircFun_eq n hn (rankFold n (uVec hk1 t)) (lt_trans (rankFold_lt n _ hrt) (tailCount_top_lt n hn)),
            unrankFold_rankFold n _ hrt]
        have h2 : unrankCircFun n B (rankCircFun n B (uVec hk1 a)) = uVec hk1 a := by
          rw [rankCircFun_eq n hn (uVec hk1 a) hra,
            unrankCircFun_eq n hn (rankFold n (uVec hk1 a)) (lt_trans (rankFold_lt n _ hra) (tailCount_top_lt n hn)),
            unrankFold_rankFold n _ hra]
        rw [← h1, ← h2, hrk_eq]
      have hz_eq : t.2 = a.2 := by
        funext j
        have hj := congrFun hu_eq j
        unfold uVec xPref at hj
        rw [hx_eq] at hj
        revert hj
        cases a.1 ⟨j.val, by omega⟩ <;> cases t.2 j <;> cases a.2 j <;> decide
      exact ⟨Prod.ext hab (hz_eq.symm.trans hbt.symm), Prod.ext (hab.symm.trans hx_eq.symm) hbt⟩
    ·
      have hflt : flagBit hk1 t = true := hfl_bt.symm.trans hflb
      have hfla : flagBit hk1 a = true := hfl_ta.symm.trans hflt
      have htt_eq : ∀ j : Fin c, tagTrueFun k hk H (rawVec t) j = tagTrueFun k hk H (rawVec a) j := by
        intro j
        have hj := congrFun htt j
        change tagCircFun k hk H (rawVec t) j = tagCircFun k hk H (rawVec a) j at hj
        unfold tagCircFun at hj
        rw [hu_raw t, hu_raw a] at hj
        change (if flagBit hk1 t then tagTrueFun k hk H (rawVec t) j else tagFalseFun k hk (rawVec t) j) =
          (if flagBit hk1 a then tagTrueFun k hk H (rawVec a) j else tagFalseFun k hk (rawVec a) j) at hj
        simpa [hflt, hfla] using hj
      have hsp_eq : t.1 ⟨n, by omega⟩ = a.1 ⟨n, by omega⟩ := by
        have h1 := htt_eq ⟨1, by omega⟩
        unfold tagTrueFun at h1
        simp only [show (1 : ℕ) ≠ 0 by omega, ↓reduceIte] at h1
        rwa [hraw_get1 t ⟨n, by omega⟩, hraw_get1 a ⟨n, by omega⟩] at h1
      have hpk_eq : packAllTrits n (xPref hk1 t) t.2 = packAllTrits n (xPref hk1 a) a.2 := by
        funext j
        have hj := htt_eq ⟨2 + j.val, by omega⟩
        unfold tagTrueFun at hj
        have h0 : ¬ (2 + j.val = 0) := by omega
        have h1 : ¬ (2 + j.val = 1) := by omega
        have h2 : 2 + j.val < 2 + (k - 1 + 4) / 5 * 8 := by omega
        simp only [h0, h1, ↓reduceIte, h2, ↓reduceDIte, Nat.add_sub_cancel_left] at hj
        have hxp_t : (fun i : Fin n => rawVec t ⟨i.val, by omega⟩) = xPref hk1 t :=
          funext fun i => hraw_get1 t ⟨i.val, by omega⟩
        have hzp_t : (fun i : Fin n => rawVec t ⟨k + i.val, by omega⟩) = t.2 :=
          funext fun i => hraw_get2 t i
        have hxp_a : (fun i : Fin n => rawVec a ⟨i.val, by omega⟩) = xPref hk1 a :=
          funext fun i => hraw_get1 a ⟨i.val, by omega⟩
        have hzp_a : (fun i : Fin n => rawVec a ⟨k + i.val, by omega⟩) = a.2 :=
          funext fun i => hraw_get2 a i
        rwa [hxp_t, hzp_t, hxp_a, hzp_a] at hj
      have hsyn_eq : syndrome H (xPref hk1 t) = syndrome H (xPref hk1 a) := by
        funext j
        have hj := htt_eq ⟨2 + q * 8 + j.val, by omega⟩
        unfold tagTrueFun at hj
        have h0 : ¬ (2 + q * 8 + j.val = 0) := by omega
        have h1 : ¬ (2 + q * 8 + j.val = 1) := by omega
        have h2 : ¬ (2 + q * 8 + j.val < 2 + (k - 1 + 4) / 5 * 8) := by omega
        have h3 : 2 + q * 8 + j.val < 2 + (k - 1 + 4) / 5 * 8 + (3 * (k - 1) + 7) / 8 := by
          have : (k - 1 + 4) / 5 = q := rfl
          have : (3 * (k - 1) + 7) / 8 = r := rfl
          have := j.isLt
          omega
        simp only [h0, h1, ↓reduceIte, h2, h3, ↓reduceDIte] at hj
        have hsub : 2 + q * 8 + j.val - (2 + (k - 1 + 4) / 5 * 8) = j.val := by
          have : (k - 1 + 4) / 5 = q := rfl
          omega
        simp only [hsub] at hj
        have hxp_t : (fun i : Fin n => rawVec t ⟨i.val, by omega⟩) = xPref hk1 t :=
          funext fun i => hraw_get1 t ⟨i.val, by omega⟩
        have hxp_a : (fun i : Fin n => rawVec a ⟨i.val, by omega⟩) = xPref hk1 a :=
          funext fun i => hraw_get1 a ⟨i.val, by omega⟩
        rwa [hxp_t, hxp_a] at hj
      let Δ : Fin n → Bool := fun j => Bool.xor (xPref hk1 t j) (xPref hk1 b j)
      have hcoord : ∀ j : Fin n,
          (uVec hk1 t j).toNat = (uVec hk1 b j).toNat + (Δ j).toNat ∧
          Bool.xor (a.2 j) (b.2 j) = Δ j := by
        intro j
        have hsum := packAllTrits_eq_imp hpk_eq j
        have hxa : xPref hk1 a j = xPref hk1 b j := by unfold xPref; rw [hab]
        have hzt : t.2 j = b.2 j := by rw [hbt]
        rw [hxa, hzt] at hsum
        dsimp only [uVec, Δ]
        rw [hzt]
        revert hsum
        cases xPref hk1 b j <;> cases b.2 j <;> cases xPref hk1 t j <;> cases a.2 j <;> decide
      have hpop_t : popcountVal (uVec hk1 t) = popcountVal (uVec hk1 b) + popcountVal Δ := by
        unfold popcountVal
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _; exact (hcoord j).1
      have hband_b : 16 * Nat.dist (2 * popcountVal (uVec hk1 b)) n ≤ n := by
        unfold flagBit at hflb; exact of_decide_eq_true hflb
      have hband_t : 16 * Nat.dist (2 * popcountVal (uVec hk1 t)) n ≤ n := by
        unfold flagBit at hflt; exact of_decide_eq_true hflt
      have hbi_b := (band_iff_interval n (popcountVal (uVec hk1 b))).mp hband_b
      have hbi_t := (band_iff_interval n (popcountVal (uVec hk1 t))).mp hband_t
      have hwt_le : popcountVal Δ ≤ n / 16 := by omega
      have hsyn_Δ : syndrome H Δ = fun _ => false := by
        funext row
        have hxab : xPref hk1 a = xPref hk1 b := by funext j; unfold xPref; rw [hab]
        rw [syndrome_xor H (xPref hk1 t) (xPref hk1 b) row, ← hxab, hsyn_eq]
        cases syndrome H (xPref hk1 a) row <;> rfl
      have hΔ0 : ∀ j : Fin n, Δ j = false := by
        intro j
        by_contra hne
        have hj : Δ j = true := by cases h : Δ j <;> simp_all
        exact hH Δ ⟨j, hj⟩ hwt_le hsyn_Δ
      have hxt_eq : t.1 = b.1 := by
        funext j
        by_cases hjn : j.val < n
        · have h0 := hΔ0 ⟨j.val, hjn⟩
          dsimp only [Δ, xPref] at h0
          cases h1 : t.1 j <;> cases h2 : b.1 j <;> simp_all
        · have hj_last : j = ⟨n, by omega⟩ := Fin.ext (by have := j.isLt; simp; omega)
          rw [hj_last, hsp_eq, hab]
      have hza_eq : a.2 = b.2 := by
        funext j
        have h0 := (hcoord j).2.trans (hΔ0 j)
        revert h0
        cases a.2 j <;> cases b.2 j <;> decide
      exact ⟨Prod.ext hab hza_eq, Prod.ext hxt_eq.symm hbt⟩
  ·
    intro e
    fin_cases e
    ·
      dsimp only
      refine ⟨⟨[], 0⟩, fun j => ⟨j.val, by have := j.isLt; simp [Circuit.size]; omega⟩,
        ⟨fun j hj => by simp at hj, by simp [Circuit.size], fun g hg => by simp at hg⟩, ?_⟩
      intro w j
      have h0_0 : ((⟨0, by decide⟩ : Fin 3) = 0) := rfl
      simp only [h0_0, ↓reduceIte]
      change (List.ofFn w.1 ++ (List.ofFn w.2 ++ List.ofFn _)).getD j.val false =
        (List.ofFn w.1 ++ List.ofFn w.2).getD j.val false
      rw [← List.append_assoc, getD_append_left _ _ _ _ (by simp)]
    ·
      dsimp only
      have h1_0 : ((1 : Fin 3) ≠ 0) := by decide
      have h1_2 : ((1 : Fin 3) ≠ 2) := by decide
      have h1p_2 : ((1 : Fin 3) + 1 = 2) := rfl
      have h2_0 : ((2 : Fin 3) ≠ 0) := by decide
      have h2_1 : ((2 : Fin 3) ≠ 1) := by decide
      have h1_eq : (⟨1, by decide⟩ : Fin 3) = 1 := rfl
      simp only [h1_eq, h1_0, h1_2, h1p_2, h2_0, h2_1, ↓reduceIte]
      rcases HasCirc.dec1Circ k hk with ⟨dec, dw, hrb_d, hvg_d, hsz_d, hev_d⟩
      refine ⟨dec, dw, ⟨hrb_d, hsz_d, hvg_d⟩, ?_⟩
      intro w j
      let inp : Fin (k + c) → Bool := fun i =>
        if h1 : i.val < n then w.2 ⟨i.val, h1⟩
        else if h2 : i.val < k then flagBit hk1 w
        else tag w ⟨i.val - k, by omega⟩
      have hport_eq : (List.ofFn w.2 ++ List.ofFn (fun _ : Fin 1 =>
          decide (16 * Nat.dist (2 * (Finset.univ.filter (fun j : Fin n =>
            (List.ofFn w.1).getD j.val false ≠ w.2 j)).card) n ≤ n))) ++ List.ofFn (tag w) =
          List.ofFn inp := by
        apply list_eq_ofFn
        · simp; omega
        · intro i
          dsimp only [inp]
          by_cases h1 : i.val < n
          · simp only [h1, ↓reduceDIte]
            rw [getD_append_left _ _ _ _ (by simp; omega), getD_append_left _ _ _ _ (by simp; omega),
              List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn]
          · by_cases h2 : i.val < k
            · simp only [h1, h2, ↓reduceDIte]
              rw [getD_append_left _ _ _ _ (by simp; omega), getD_append_right _ _ _ _ (by simp; omega),
                List.length_ofFn, List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn]
              exact (flagBit_eq hk1 w).symm
            · simp only [h1, h2, ↓reduceDIte]
              rw [getD_append_right _ _ _ _ (by simp; omega), List.length_append, List.length_ofFn,
                List.length_ofFn, show n + 1 = k by omega,
                List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn]
      rw [hport_eq, hev_d inp j, hraw_eq w, List.getD_eq_getElem _ _ (by simp; exact j.isLt), List.getElem_ofFn]
      have hz_in : (fun i : Fin (k - 1) => inp ⟨i.val, by omega⟩) = w.2 := by
        funext i; simp [inp, n, i.isLt]
      have htg_pt : ∀ (a : ℕ) (ha : a < c), inp ⟨k + a, by omega⟩ = tag w ⟨a, ha⟩ := by
        intro a ha
        have h1 : ¬ (k + a < n) := by omega
        have h2 : ¬ (k + a < k) := by omega
        simp [inp, h1, h2]
      have hrec_x : (fun i : Fin k =>
          if inp ⟨k + 0, by omega⟩ then
            (if h : i.val < k - 1 then
              unpackPartner (k - 1) (fun a : Fin (((k - 1) + 4) / 5 * 8) => inp ⟨k + (2 + a.val), by omega⟩)
                (fun t : Fin (k - 1) => inp ⟨t.val, by omega⟩) ⟨i.val, h⟩
             else inp ⟨k + 1, by omega⟩)
          else inp ⟨k + (1 + i.val), by omega⟩) = w.1 := by
        funext i
        rw [hz_in, htg_pt 0 (by omega), htg_pt 1 (by omega), htg_pt (1 + i.val) (by omega), htag0 w]
        have hu_raw : (fun j : Fin n => Bool.xor (rawVec w ⟨j.val, by omega⟩) (rawVec w ⟨k + j.val, by omega⟩)) = uVec hk1 w := by
          funext t; unfold uVec xPref; rw [hraw_get1 w ⟨t.val, by omega⟩, hraw_get2 w t]
        cases hfl : flagBit hk1 w
        · simp only [Bool.false_eq_true, ↓reduceIte]
          change tagCircFun k hk H (rawVec w) ⟨1 + i.val, by omega⟩ = w.1 i
          unfold tagCircFun
          rw [hu_raw]
          change (if flagBit hk1 w then _ else tagFalseFun k hk (rawVec w) ⟨1 + i.val, by omega⟩) = w.1 i
          rw [hfl]
          unfold tagFalseFun
          have h0 : ¬ (1 + i.val = 0) := by omega
          have h1 : 1 + i.val < 1 + k := by omega
          simp only [Bool.false_eq_true, ↓reduceIte, h0, h1, ↓reduceDIte, Nat.add_sub_cancel_left]
          exact hraw_get1 w i
        · simp only [↓reduceIte]
          have htt : ∀ j : Fin c, tag w j = tagTrueFun k hk H (rawVec w) j := by
            intro j
            change tagCircFun k hk H (rawVec w) j = _
            unfold tagCircFun; rw [hu_raw]
            change (if flagBit hk1 w then _ else _) = _
            rw [hfl]; simp
          by_cases hin : i.val < k - 1
          · simp only [hin, ↓reduceDIte]
            have hpk : (fun a : Fin (((k - 1) + 4) / 5 * 8) => inp ⟨k + (2 + a.val), by omega⟩) =
                packAllTrits (k - 1) (xPref hk1 w) w.2 := by
              funext a
              rw [htg_pt (2 + a.val) (by omega), htt ⟨2 + a.val, by omega⟩]
              unfold tagTrueFun
              have h0 : ¬ (2 + a.val = 0) := by omega
              have h1 : ¬ (2 + a.val = 1) := by omega
              have h2 : 2 + a.val < 2 + (k - 1 + 4) / 5 * 8 := by omega
              simp only [h0, h1, ↓reduceIte, h2, ↓reduceDIte, Nat.add_sub_cancel_left]
              have hxp : (fun t : Fin n => rawVec w ⟨t.val, by omega⟩) = xPref hk1 w :=
                funext fun t => hraw_get1 w ⟨t.val, by omega⟩
              have hzp : (fun t : Fin n => rawVec w ⟨k + t.val, by omega⟩) = w.2 :=
                funext fun t => hraw_get2 w t
              rw [hxp, hzp]
            rw [hpk, unpackPartner_left]
            rfl
          · simp only [hin, ↓reduceDIte]
            rw [htt ⟨1, by omega⟩]
            unfold tagTrueFun
            simp only [show (1 : ℕ) ≠ 0 by omega, ↓reduceIte]
            rw [hraw_get1 w ⟨n, by omega⟩]
            exact congrArg w.1 (Fin.ext (by have := i.isLt; simp; omega))
      exact congrFun (congrArg₂ Fin.append hrec_x hz_in) j
    ·
      dsimp only
      have h2_0 : ((2 : Fin 3) ≠ 0) := by decide
      have h2_1 : ((2 : Fin 3) ≠ 1) := by decide
      have h2p_0 : ((2 : Fin 3) + 1 = 0) := rfl
      have h2p_2 : ((2 : Fin 3) + 1 ≠ 2) := by decide
      have h2_eq : (⟨2, by decide⟩ : Fin 3) = 2 := rfl
      simp only [h2_eq, h2_0, h2_1, h2p_0, h2p_2, ↓reduceIte]
      rcases HasCirc.dec2Circ k hk with ⟨dec, dw, hrb_d, hvg_d, hsz_d, hev_d⟩
      refine ⟨dec, dw, ⟨hrb_d, hsz_d, hvg_d⟩, ?_⟩
      intro w j
      let inp : Fin (c + k) → Bool := Fin.append (tag w) w.1
      have hport_eq : List.ofFn (tag w) ++ List.ofFn w.1 = List.ofFn inp := by
        apply list_eq_ofFn
        · simp
        · intro i
          by_cases h1 : i.val < c
          · rw [getD_append_left _ _ _ _ (by simp [h1]), List.getD_eq_getElem _ _ (by simp [h1]),
              List.getElem_ofFn]
            change tag w ⟨i.val, h1⟩ = Fin.append (tag w) w.1 (Fin.castAdd k ⟨i.val, h1⟩)
            rw [Fin.append_left]
          · rw [getD_append_right _ _ _ _ (by simp; omega), List.length_ofFn,
              List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn]
            have hnat : i = Fin.natAdd c ⟨i.val - c, by omega⟩ := by
              apply Fin.ext; simp [Fin.natAdd]; omega
            conv_rhs => dsimp only [inp]; rw [hnat]
            exact (Fin.append_right (tag w) w.1 ⟨i.val - c, by omega⟩).symm
      rw [hport_eq, hev_d inp j, hraw_eq w, List.getD_eq_getElem _ _ (by simp; exact j.isLt), List.getElem_ofFn]
      have htg_pt : ∀ (a : ℕ) (ha : a < c), inp ⟨a, by omega⟩ = tag w ⟨a, ha⟩ := by
        intro a ha
        change Fin.append (tag w) w.1 (Fin.castAdd k ⟨a, ha⟩) = tag w ⟨a, ha⟩
        rw [Fin.append_left]
      have hx_pt : ∀ (a : ℕ) (ha : a < k), inp ⟨2 * k - k / 1024 + a, by omega⟩ = w.1 ⟨a, ha⟩ := by
        intro a ha
        have : (⟨2 * k - k / 1024 + a, by omega⟩ : Fin (c + k)) = Fin.natAdd c ⟨a, ha⟩ := by
          apply Fin.ext; simp [Fin.natAdd, c]
        dsimp only [inp]; rw [this, Fin.append_right]
      have hx_eq : (fun i : Fin k => inp ⟨2 * k - k / 1024 + i.val, by omega⟩) = w.1 :=
        funext fun i => hx_pt i.val i.isLt
      have hrec_z : (fun i : Fin (k - 1) =>
          if inp ⟨0, by omega⟩ then
            unpackPartner (k - 1) (fun a : Fin (((k - 1) + 4) / 5 * 8) => inp ⟨2 + a.val, by omega⟩)
              (fun t : Fin (k - 1) => inp ⟨2 * k - k / 1024 + t.val, by omega⟩) i
          else
            Bool.xor (inp ⟨2 * k - k / 1024 + i.val, by omega⟩)
              (unrankCircFun (k - 1) (k - 1 - (k - 1) / 384 + 2)
                (fun b : Fin (k - 1 - (k - 1) / 384 + 2) => inp ⟨1 + k + b.val, by omega⟩) i)) = w.2 := by
        funext i
        rw [htg_pt 0 (by omega), hx_pt i.val (by omega), htag0 w]
        have hu_raw : (fun t : Fin n => Bool.xor (rawVec w ⟨t.val, by omega⟩) (rawVec w ⟨k + t.val, by omega⟩)) = uVec hk1 w := by
          funext t; unfold uVec xPref; rw [hraw_get1 w ⟨t.val, by omega⟩, hraw_get2 w t]
        cases hfl : flagBit hk1 w
        · simp only [Bool.false_eq_true, ↓reduceIte]
          have hrk_tag : (fun b : Fin (k - 1 - (k - 1) / 384 + 2) => inp ⟨1 + k + b.val, by omega⟩) =
              rankCircFun n B (uVec hk1 w) := by
            funext b
            rw [htg_pt (1 + k + b.val) (by omega)]
            change tagCircFun k hk H (rawVec w) ⟨1 + k + b.val, by omega⟩ = _
            unfold tagCircFun; rw [hu_raw]
            change (if flagBit hk1 w then _ else tagFalseFun k hk (rawVec w) ⟨1 + k + b.val, by omega⟩) = _
            rw [hfl]
            unfold tagFalseFun
            have h0 : ¬ (1 + k + b.val = 0) := by omega
            have h1 : ¬ (1 + k + b.val < 1 + k) := by omega
            have h2 : 1 + k + b.val < 1 + k + (k - 1 - (k - 1) / 384 + 2) := by omega
            simp only [Bool.false_eq_true, ↓reduceIte, h0, h1, h2, ↓reduceDIte, Nat.add_sub_cancel_left]
            rw [hu_raw]
          have hrare : isRare n (popcountVal (uVec hk1 w)) = true := by
            unfold isRare; unfold flagBit at hfl; rw [hfl]; rfl
          rw [hrk_tag, rankCircFun_eq n hn (uVec hk1 w) hrare,
            unrankCircFun_eq n hn (rankFold n (uVec hk1 w))
              (lt_trans (rankFold_lt n _ hrare) (tailCount_top_lt n hn)),
            unrankFold_rankFold n _ hrare]
          unfold uVec xPref
          cases w.1 ⟨i.val, by omega⟩ <;> cases w.2 i <;> rfl
        · simp only [↓reduceIte]
          have hpk : (fun a : Fin (((k - 1) + 4) / 5 * 8) => inp ⟨2 + a.val, by omega⟩) =
              packAllTrits (k - 1) (xPref hk1 w) w.2 := by
            funext a
            rw [htg_pt (2 + a.val) (by omega)]
            change tagCircFun k hk H (rawVec w) ⟨2 + a.val, by omega⟩ = _
            unfold tagCircFun; rw [hu_raw]
            change (if flagBit hk1 w then tagTrueFun k hk H (rawVec w) ⟨2 + a.val, by omega⟩ else _) = _
            rw [hfl]
            unfold tagTrueFun
            have h0 : ¬ (2 + a.val = 0) := by omega
            have h1 : ¬ (2 + a.val = 1) := by omega
            have h2 : 2 + a.val < 2 + (k - 1 + 4) / 5 * 8 := by omega
            simp only [↓reduceIte, h0, h1, h2, ↓reduceDIte, Nat.add_sub_cancel_left]
            have hxp : (fun t : Fin n => rawVec w ⟨t.val, by omega⟩) = xPref hk1 w :=
              funext fun t => hraw_get1 w ⟨t.val, by omega⟩
            have hzp : (fun t : Fin n => rawVec w ⟨k + t.val, by omega⟩) = w.2 :=
              funext fun t => hraw_get2 w t
            rw [hxp, hzp]
          have hxp2 : (fun t : Fin (k - 1) => inp ⟨2 * k - k / 1024 + t.val, by omega⟩) = xPref hk1 w :=
            funext fun t => hx_pt t.val (by omega)
          rw [hpk, hxp2]
          exact congrFun (unpackPartner_right (xPref hk1 w) w.2) i
      exact congrFun (congrArg₂ Fin.append hx_eq hrec_z) j
  ·
    rcases HasCirc.flagCirc k (by omega) with ⟨gate, gout, hrb_g, hvg_g, hsz_g, hev_g⟩
    refine ⟨gate, gout 0, ⟨hrb_g, hsz_g, hvg_g⟩, ?_⟩
    intro w
    rw [hraw_eq w, hev_g (rawVec w) 0, ← flagBit_eq hk1 w]
    dsimp only
    unfold flagBit uVec xPref
    have hu : (fun j : Fin n => Bool.xor (rawVec w ⟨j.val, by omega⟩) (rawVec w ⟨k + j.val, by omega⟩)) =
        fun j : Fin n => Bool.xor (w.1 ⟨j.val, by omega⟩) (w.2 j) := by
      funext j; rw [hraw_get1 w ⟨j.val, by omega⟩, hraw_get2 w j]
    rw [hu]

