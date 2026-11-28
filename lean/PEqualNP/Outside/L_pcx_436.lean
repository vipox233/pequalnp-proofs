import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_436_aux

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

lemma HasCirc.constBits {n B : ℕ} (hn : 0 < n) (val : ℕ) :
    HasCirc n B (2 * B) (fun _ => natToBits B val) := by
  have h := HasCirc.vecConst (n := n) (m := B) (B := 2) (f := fun _ => natToBits B val)
    (fun j => HasCirc.const hn (val.testBit j.val))
  simpa [Nat.mul_comm] using h

theorem bitsToNat_truncate (w x : ℕ) : bitsToNat (natToBits w x) = x % 2^w := by
  have hmod : x % 2^w < 2^w := Nat.mod_lt _ (by positivity)
  rw [← bitsToNat_natToBits hmod]
  congr 1
  funext j
  simp [natToBits, Nat.testBit_mod_two_pow, j.isLt]

theorem HasCirc.reindex {n k m B : ℕ} {f : (Fin k → Bool) → Fin m → Bool}
    (h : HasCirc k m B f) (inp : Fin k → Fin n) :
    HasCirc n m B (fun x => f (fun j => x (inp j))) := by
  simpa using HasCirc.comp (HasCirc.proj inp) h

theorem HasCirc.outputs {n k m B : ℕ} {f : (Fin n → Bool) → Fin k → Bool}
    (h : HasCirc n k B f) (out : Fin m → Fin k) :
    HasCirc n m B (fun x j => f x (out j)) := by
  simpa using HasCirc.comp h (HasCirc.proj out)

theorem HasCirc.addWords {n w A B : ℕ} (hw : 0 < w)
    {f g : (Fin n → Bool) → Fin w → Bool} (hf : HasCirc n w A f) (hg : HasCirc n w B g) :
    HasCirc n w (A+B+(16*w+2))
      (fun x => natToBits w (bitsToNat (f x) + bitsToNat (g x))) := by
  refine ((HasCirc.comp (HasCirc.pair hf hg) (HasCirc.addB w hw)).outputs Fin.castSucc).congr ?_
  intro x j
  change natToBits (w + 1) (bitsToNat (fun i : Fin w => Fin.append (f x) (g x) (i.castAdd w)) +
    bitsToNat (fun i : Fin w => Fin.append (f x) (g x) (i.natAdd w))) j.castSucc = _
  simp only [Fin.append_left, Fin.append_right, natToBits, Fin.val_castSucc]

theorem HasCirc.geWords {n w A B : ℕ} (hw : 0 < w)
    {f g : (Fin n → Bool) → Fin w → Bool} (hf : HasCirc n w A f) (hg : HasCirc n w B g) :
    HasCirc n 1 (A+B+(16*w+w+5))
      (fun x _ => decide (bitsToNat (g x) ≤ bitsToNat (f x))) := by
  refine ((HasCirc.comp (HasCirc.pair hf hg) (HasCirc.subCmp w hw)).outputs
    (fun _ : Fin 1 => Fin.last w)).weaken ?_ |>.congr ?_
  · omega
  intro x _
  rw [subCmpFun_top]
  change (decide (bitsToNat (fun i : Fin w => Fin.append (f x) (g x) (i.natAdd w)) ≤
    bitsToNat (fun i : Fin w => Fin.append (f x) (g x) (i.castAdd w)))) = _
  simp only [Fin.append_left, Fin.append_right]

theorem HasCirc.muxWords {n w A B C : ℕ} {sel : (Fin n → Bool) → Fin 1 → Bool}
    {f g : (Fin n → Bool) → Fin w → Bool} (hs : HasCirc n 1 A sel)
    (hf : HasCirc n w B f) (hg : HasCirc n w C g) :
    HasCirc n w (A+(B+C)+4*w) (fun x j => if sel x 0 then f x j else g x j) := by
  have hsrc := HasCirc.pair hs (HasCirc.pair hf hg)
  have hi : HasCirc (1+(w+w)) w (w*4)
      (fun x j => if x (Fin.castAdd (w+w) 0) then
        x (Fin.natAdd 1 (Fin.castAdd w j)) else x (Fin.natAdd 1 (Fin.natAdd w j))) := by
    apply HasCirc.vecConst
    intro j
    let p (i : Fin 3) : Fin (1+(w+w)) := ![Fin.castAdd (w+w) 0,
      Fin.natAdd 1 (Fin.castAdd w j), Fin.natAdd 1 (Fin.natAdd w j)] i
    exact HasCirc.iteGate.reindex p |>.congr (by intro x j; simp [p])
  refine (HasCirc.comp hsrc hi).weaken (by omega) |>.congr ?_
  intro x j
  simp only [Fin.append_left, Fin.append_right]

theorem HasCirc.shiftLeft {n w A : ℕ} (hn : 0 < n) (k : ℕ)
    {f : (Fin n → Bool) → Fin w → Bool} (hf : HasCirc n w A f) :
    HasCirc n w (A+2)
      (fun x j => if h : k ≤ j.val then f x ⟨j.val-k, by omega⟩ else false) := by
  have hc := HasCirc.const hn false
  let idx (j : Fin w) : Fin (w+1) := if h : k ≤ j.val then
    Fin.castAdd 1 ⟨j.val-k, by omega⟩ else Fin.natAdd w 0
  refine ((HasCirc.pair hf hc).outputs idx).congr ?_
  intro x j
  by_cases h : k ≤ j.val
  · simp only [idx, dite_eq_left h, Fin.append_left]
  · simp only [idx, dite_eq_right h, Fin.append_right]

theorem shiftBits (w k x : ℕ) (j : Fin w) :
    (if h : k ≤ j.val then natToBits w x ⟨j.val-k, by omega⟩ else false) =
      natToBits w (x * 2^k) j := by
  simp only [natToBits, ← Nat.shiftLeft_eq]
  rw [Nat.testBit_shiftLeft]
  by_cases h : k ≤ j.val <;> simp [h]

theorem natToBits_mod (w x : ℕ) : natToBits w (x % 2^w) = natToBits w x := by
  funext j
  simp [natToBits, Nat.testBit_mod_two_pow, j.isLt]

theorem HasCirc.scale (w width c : ℕ) (hw : 0 < w) (hc : c < 2^width) :
    HasCirc w w (2*w+width*(18*w+4)) (fun x => natToBits w (bitsToNat x * c)) := by
  induction width generalizing c with
  | zero =>
    have hzero : c = 0 := by simp at hc; omega
    subst c
    simpa using HasCirc.constBits hw 0
  | succ k ih =>
    have hdiv : c / 2 < 2^k := by
      simpa [pow_succ, Nat.mul_comm] using (Nat.div_lt_iff_lt_mul (by decide : 0 < 2)).mpr hc
    have ha := HasCirc.shiftLeft hw 1 (ih (c/2) hdiv)
    have ha' : HasCirc w w (2*w+k*(18*w+4)+2) (fun x : Fin w → Bool => natToBits w (bitsToNat x * ((c/2)*2))) := by
      apply ha.congr
      intro x j
      simpa only [pow_one, mul_assoc] using shiftBits w 1 (bitsToNat x * (c/2)) j
    have hb : HasCirc w w (2*w) (fun x : Fin w → Bool => natToBits w (bitsToNat x * (c%2))) := by
      have hb2 : c%2 < 2 := Nat.mod_lt _ (by decide)
      by_cases hb0 : c%2 = 0
      · simpa [hb0] using HasCirc.constBits hw 0
      · have hb1 : c%2 = 1 := by omega
        simpa only [hb1, mul_one, natToBits_bitsToNat, id_eq] using (HasCirc.proj (id : Fin w → Fin w)).weaken
          (Nat.zero_le (2*w))
    refine ((HasCirc.addWords hw ha' hb).weaken ?_).congr ?_
    · simp only [Nat.add_mul, one_mul]
      omega
    · intro x j
      simp only [bitsToNat_truncate]
      have h := Nat.mod_add_div c 2
      have hs : bitsToNat x * (c / 2 * 2) + bitsToNat x * (c % 2) = bitsToNat x * c := by
        rw [← mul_add]
        congr 1
        omega
      rw [← natToBits_mod, ← Nat.add_mod, natToBits_mod, hs]

theorem HasCirc.subWrapWords {n w A B : ℕ} (hw : 0 < w)
    {f g : (Fin n → Bool) → Fin w → Bool} (hf : HasCirc n w A f) (hg : HasCirc n w B g) :
    HasCirc n w (A+B+(16*w+w+5))
      (fun x => natToBits w (2^w + bitsToNat (f x) - bitsToNat (g x))) := by
  refine (((HasCirc.comp (HasCirc.pair hf hg) (HasCirc.subCmp w hw)).outputs Fin.castSucc).weaken
    (by omega)).congr ?_
  intro x j
  change natToBits (w + 1) (1 + bitsToNat (fun i : Fin w => Fin.append (f x) (g x) (i.castAdd w)) +
    (2^w - 1 - bitsToNat (fun i : Fin w => Fin.append (f x) (g x) (i.natAdd w)))) j.castSucc = _
  simp only [Fin.append_left, Fin.append_right, natToBits, Fin.val_castSucc]
  congr 1
  change 1 + bitsToNat (f x) + (2^w-1-bitsToNat (g x)) =
    2^w + bitsToNat (f x) - bitsToNat (g x)
  have h := bitsToNat_lt (g x)
  omega

theorem fold_add_nat {I : Type*} (w : ℕ) (l : List I) (a : I → ℕ)
    (start : Fin w → Bool) :
    (l.foldl (fun st i => natToBits w (bitsToNat st + a i)) start) =
      natToBits w (bitsToNat start + (l.map a).sum) := by
  induction l generalizing start with
  | nil => simp [natToBits_bitsToNat]
  | cons v l ih =>
    rw [List.foldl_cons, ih]
    simp only [bitsToNat_truncate, List.map_cons, List.sum_cons]
    rw [← Nat.add_assoc (bitsToNat start) (a v) (l.map a).sum]
    have he : ((bitsToNat start + a v) % 2^w + (l.map a).sum) % 2^w =
        (bitsToNat start + a v + (l.map a).sum) % 2^w := by
      rw [Nat.add_mod ((bitsToNat start + a v) % 2^w), Nat.mod_mod,
        ← Nat.add_mod (bitsToNat start + a v)]
    rw [← natToBits_mod, he, natToBits_mod]

theorem HasCirc.sumWords {n w k B : ℕ} (hn : 0 < n) (hw : 0 < w)
    {f : Fin k → (Fin n → Bool) → Fin w → Bool} (hf : ∀ i, HasCirc n w B (f i)) :
    HasCirc n w (2*w+k*(B+(16*w+2))) (fun x =>
      natToBits w (∑ i : Fin k, bitsToNat (f i x))) := by
  let step (i : Fin k) (x : Fin (n+w) → Bool) := natToBits w
    (bitsToNat (fun j : Fin w => x (j.natAdd n)) +
      bitsToNat (f i (fun j : Fin n => x (j.castAdd w))))
  have hstep (i : Fin k) : HasCirc (n+w) w (B+(16*w+2)) (step i) := by
    simpa [step] using HasCirc.addWords hw (HasCirc.proj (Fin.natAdd n : Fin w → Fin (n+w)))
      ((hf i).reindex (Fin.castAdd w))
  refine (HasCirc.foldl (HasCirc.constBits hn 0) k step hstep).congr ?_
  intro x j
  simp only [step, Fin.append_left, Fin.append_right]
  rw [fold_add_nat, ← List.ofFn_eq_map, List.sum_ofFn]
  have hzero := bitsToNat_natToBits (B := w) (show 0 < 2^w by positivity)
  rw [hzero, zero_add]

theorem HasCirc.fromCircuit {n m s : ℕ} (g : Circuit)
    (out : Fin m → Fin (n+g.size)) (hv : ReadsBack n g)
    (hvg : ∀ g' ∈ g.gates, ValidGate g') (hs : g.size ≤ s) :
    HasCirc n m s (fun x j => (g.wires (List.ofFn x)).getD (out j).val false) :=
  ⟨g, out, hv, hvg, hs, fun _ _ => rfl⟩

def encodeBlocks {l w : ℕ} (hw : 0 < w) (f : Fin l → Fin w → Bool) : Fin (l*w) → Bool :=
  fun j => f ⟨j.val / w, div_lt_of_lt_mul_right j.isLt⟩ ⟨j.val % w, Nat.mod_lt _ hw⟩

theorem encodeBlocks_ofFn {l w : ℕ} (hw : 0 < w) (f : Fin l → Fin w → Bool) :
    List.ofFn (encodeBlocks hw f) = (List.ofFn fun e => List.ofFn (f e)).flatten := by
  rw [List.ofFn_mul]
  congr 1
  congr 1
  funext e
  congr 1
  funext j
  have hq : (e.val*w+j.val)/w = e.val := by
    have h1 : e.val*w ≤ e.val*w+j.val := by omega
    have h2 : e.val*w+j.val < (e.val+1)*w := by rw [Nat.add_mul]; simp
    exact Nat.div_eq_of_lt_le h1 h2
  have hm : (e.val*w+j.val)%w = j.val := by
    rw [Nat.add_mod, Nat.mul_mod_left, zero_add, Nat.mod_mod, Nat.mod_eq_of_lt j.isLt]
  unfold encodeBlocks
  congr 1
  · exact Fin.ext hq
  · exact Fin.ext hm

def edgeWord {l B : ℕ} (w : Fin l → Bool → Fin (2^B)) (e : Fin l) : Fin (B+B) → Bool :=
  Fin.append (natToBits B (w e false).val) (natToBits B (w e true).val)

theorem edgeWord_ofFn {l B : ℕ} (w : Fin l → Bool → Fin (2^B)) (e : Fin l) :
    List.ofFn (edgeWord w e) =
      List.ofFn (fun i : Fin B => (w e false).val.testBit i.val) ++
        List.ofFn (fun i : Fin B => (w e true).val.testBit i.val) := by
  rw [edgeWord, List.ofFn_fin_append]
  rfl

theorem HasCirc.encodeWords {n l w X : ℕ} (hw : 0 < w)
    {f : Fin l → (Fin n → Bool) → (Fin w → Bool)} (hf : ∀ e, HasCirc n w X (f e)) :
    HasCirc n (l*w) (l*X) (fun x => encodeBlocks hw (fun e => f e x)) :=
  HasCirc.finBlocks hw hf

end PEqualNP.Outside.L_pcx_436_aux

open scoped BigOperators
open Finset Polynomial

namespace PEqualNP.Outside.L_pcx_436_aux

theorem eval_neg_one (P : ℤ[X]) (M : ℕ) (hP : P.natDegree ≤ M) :
    P.eval (-1) =
      -((-1 : ℤ)^(M+1) * ∑ j ∈ range (M+1),
        ((-1 : ℤ)^(M-j) * ((M+1).choose (j+1) : ℤ)) * P.eval (j : ℤ)) := by
  have h := congrFun (Polynomial.fwdDiff_iter_eq_zero_of_degree_lt
    (P := P) (n := M+1) (Nat.lt_succ_of_le hP)) (-1)
  rw [fwdDiff_iter_eq_sum_shift, sum_range_succ'] at h
  simp only [Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, mul_one,
    zero_nsmul, add_zero, zsmul_eq_mul, Pi.zero_apply] at h
  have hj (j : ℕ) : (-1 : ℤ) + (j + 1) • (1 : ℤ) = j := by simp
  simp only [hj, Nat.succ_sub_succ_eq_sub] at h
  have hs : (-1 : ℤ)^(M+1) * (-1 : ℤ)^(M+1) = 1 := by
    rw [← mul_pow]; norm_num
  let A : ℤ := (-1)^(M+1)
  let S : ℤ := ∑ j ∈ range (M+1),
    ((-1 : ℤ)^(M-j) * ((M+1).choose (j+1) : ℤ)) * P.eval (j : ℤ)
  change S + A * P.eval (-1) = 0 at h
  have he : A * P.eval (-1) = -S := by linarith only [h]
  calc
    P.eval (-1) = A * (A * P.eval (-1)) := by rw [← mul_assoc, hs, one_mul]
    _ = -(A * S) := by rw [he, mul_neg]

def spinSign (b : Bool) : ℤ := if b then -1 else 1

theorem spinSign_xor (a b : Bool) : spinSign (xor a b) = spinSign a * spinSign b := by
  cases a <;> cases b <;> norm_num [spinSign]

theorem spinSign_sq (a : Bool) : spinSign a * spinSign a = 1 := by
  cases a <;> norm_num [spinSign]

theorem spinSign_eq_indicator (a b : Bool) :
    (1 : ℤ) + spinSign a * spinSign b = if a = b then 2 else 0 := by
  cases a <;> cases b <;> norm_num [spinSign]

theorem pin_expansion {V : Type*} [DecidableEq V] (pins : Finset V) (x p : V → Bool) :
    (∑ S ∈ pins.powerset, ∏ v ∈ S, spinSign (x v) * spinSign (p v)) =
      if ∀ v ∈ pins, x v = p v then (2 : ℤ)^pins.card else 0 := by
  rw [← show (∏ v ∈ pins, (spinSign (x v) * spinSign (p v) + 1)) =
      ∑ S ∈ pins.powerset, ∏ v ∈ S, spinSign (x v) * spinSign (p v) by
    simpa using Finset.prod_add (fun v => spinSign (x v) * spinSign (p v))
      (fun _ => (1 : ℤ)) pins]
  simp_rw [add_comm _ (1 : ℤ), spinSign_eq_indicator]
  split_ifs with h
  · rw [Finset.prod_congr rfl (fun v hv => ite_eq_left (h v hv)), Finset.prod_const]
  · push Not at h
    obtain ⟨v, hv, hn⟩ := h
    exact Finset.prod_eq_zero hv (ite_eq_right hn)

section Paths

variable {V E : Type*} (u v : E → V)

def Adj (a b : V) : Prop := ∃ e, (u e = a ∧ v e = b) ∨ (u e = b ∧ v e = a)

theorem path_character {a b : V} (h : Relation.ReflTransGen (Adj u v) a b) :
    ∃ path : List E, ∀ x : V → Bool,
      (path.map (fun e => spinSign (xor (x (u e)) (x (v e))))).prod =
        spinSign (x a) * spinSign (x b) := by
  induction h with
  | refl => exact ⟨[], fun x => (spinSign_sq (x a)).symm⟩
  | @tail y z _ hyz ih =>
    obtain ⟨path, hp⟩ := ih
    obtain ⟨e, (⟨he₁, he₂⟩ | ⟨he₁, he₂⟩)⟩ := hyz
    · refine ⟨path ++ [e], fun x => ?_⟩
      simp only [List.map_append, List.map_cons, List.map_nil, List.prod_append,
        List.prod_cons, List.prod_nil, mul_one]
      rw [hp, spinSign_xor, he₁, he₂]
      rw [mul_assoc, ← mul_assoc (spinSign (x y)), spinSign_sq, one_mul]
    · refine ⟨path ++ [e], fun x => ?_⟩
      simp only [List.map_append, List.map_cons, List.map_nil, List.prod_append,
        List.prod_cons, List.prod_nil, mul_one]
      rw [hp, spinSign_xor, he₁, he₂]
      rw [mul_comm (spinSign (x z)), mul_assoc, ← mul_assoc (spinSign (x y)),
        spinSign_sq, one_mul]

theorem path_parity [Fintype E] [DecidableEq E] (l : List E) (b : E → Bool) :
    (l.map (fun e => spinSign (b e))).prod =
      ∏ e : E, if (l.count e) % 2 = 1 then spinSign (b e) else 1 := by
  classical
  rw [Finset.prod_list_map_count]
  calc
    _ = ∏ e : E, spinSign (b e)^l.count e := by
      apply Finset.prod_subset (Finset.subset_univ _)
      intro e _ he
      rw [List.count_eq_zero_of_not_mem (fun hm => he (List.mem_toFinset.mpr hm)), pow_zero]
    _ = _ := by
      apply Finset.prod_congr rfl
      intro e _
      have hs : spinSign (b e)^2 = 1 := by rw [pow_two, spinSign_sq]
      rw [pow_eq_pow_mod _ hs]
      split_ifs with h
      · rw [h, pow_one]
      · have h0 : l.count e % 2 = 0 := by omega
        rw [h0, pow_zero]

theorem flatMap_prod {A B M : Type*} [CommMonoid M]
    (l : List A) (p : A → List B) (f : B → M) :
    ((l.flatMap p).map f).prod = (l.map fun a => ((p a).map f).prod).prod := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.flatMap_cons, List.map_append, List.prod_append, List.map_cons,
      List.prod_cons, ih]

theorem even_character [Fintype E] [DecidableEq E] (root : V)
    (connected : ∀ a, Relation.ReflTransGen (Adj u v) root a)
    (S : Finset V) (even : Even S.card) :
    ∃ mask : E → Bool, ∀ x : V → Bool,
      (∏ a ∈ S, spinSign (x a)) =
        ∏ e : E, if mask e && xor (x (u e)) (x (v e)) then -1 else 1 := by
  classical
  choose path hp using fun a => path_character u v (connected a)
  let l : List E := S.toList.flatMap path
  refine ⟨fun e => decide (l.count e % 2 = 1), fun x => ?_⟩
  have h₁ : (∏ a ∈ S, spinSign (x root) * spinSign (x a)) = ∏ a ∈ S, spinSign (x a) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const]
    have hpow : spinSign (x root)^S.card = 1 := by
      cases h : x root with
      | false => simp [spinSign]
      | true => simpa [spinSign] using even.neg_pow (1 : ℤ)
    rw [hpow, one_mul]
  rw [← h₁]
  simp_rw [← hp _ x]
  rw [← Finset.prod_map_toList, ← flatMap_prod]
  exact (path_parity l _).trans (Finset.prod_congr rfl fun e _ => by
    by_cases h : l.count e % 2 = 1 <;> simp [l, h, spinSign])

end Paths

section Complement

def complementEquiv (V : Type*) : (V → Bool) ≃ (V → Bool) where
  toFun x a := !(x a)
  invFun x a := !(x a)
  left_inv x := by funext a; simp
  right_inv x := by funext a; simp

theorem complement_disagreement {V E : Type*} (u v : E → V) (x : V → Bool) (e : E) :
    xor (complementEquiv V x (u e)) (complementEquiv V x (v e)) =
      xor (x (u e)) (x (v e)) := by
  change xor (!(x (u e))) (!(x (v e))) = _
  cases x (u e) <;> cases x (v e) <;> rfl

theorem odd_character_sum {V : Type*} [Fintype V] [DecidableEq V] (S : Finset V) (odd : Odd S.card)
    (w : (V → Bool) → ℤ) (hw : ∀ x, w (complementEquiv V x) = w x) :
    (∑ x, w x * ∏ a ∈ S, spinSign (x a)) = 0 := by
  classical
  let Q := fun x : V → Bool => w x * ∏ a ∈ S, spinSign (x a)
  have hneg (x : V → Bool) : Q (complementEquiv V x) = -Q x := by
    have hs (b : Bool) : spinSign (!b) = (-1 : ℤ) * spinSign b := by
      cases b <;> norm_num [spinSign]
    simp only [Q, hw]
    change w x * (∏ a ∈ S, spinSign (!(x a))) = _
    simp_rw [hs, Finset.prod_mul_distrib, Finset.prod_const]
    rw [show (-1 : ℤ)^S.card = -1 by simpa using odd.neg_pow (1 : ℤ)]
    ring
  have hsum := (complementEquiv V).sum_comp Q
  simp_rw [hneg, Finset.sum_neg_distrib] at hsum
  change (∑ x, Q x) = 0
  omega

end Complement

section Prefix

variable {V E : Type*} (u v : E → V)

theorem eqAlong {x t : V → Bool} {keep : V → Prop}
    (hd : ∀ e, keep (u e) → keep (v e) →
      xor (x (u e)) (x (v e)) = xor (t (u e)) (t (v e))) {a b : V}
    (h : Relation.ReflTransGen (fun i j => keep i ∧ keep j ∧ Adj u v i j) a b)
    (hb : x b = t b) : x a = t a := by
  induction h with
  | refl => exact hb
  | @tail y z _ hyz ih =>
    obtain ⟨hkeepY, hkeepZ, e, (⟨he₁, he₂⟩ | ⟨he₁, he₂⟩)⟩ := hyz
    · apply ih
      have hq := hd e (he₁ ▸ hkeepY) (he₂ ▸ hkeepZ)
      rw [he₁, he₂, hb] at hq
      cases hx : x y <;> cases ht : t y <;> cases hz : t z <;> simp_all
    · apply ih
      have hq := hd e (he₁ ▸ hkeepZ) (he₂ ▸ hkeepY)
      rw [he₁, he₂, hb] at hq
      cases hx : x y <;> cases ht : t y <;> cases hz : t z <;> simp_all

theorem prefix_constraints [DecidableEq V] {x t : V → Bool} {keep : V → Prop}
    {R : Finset V}
    (hR : ∀ a, keep a → ∃ r ∈ R, keep r ∧
      Relation.ReflTransGen (fun i j => keep i ∧ keep j ∧ Adj u v i j) a r) :
    (∀ a, keep a → x a = t a) ↔
      (∀ e, keep (u e) → keep (v e) →
        xor (x (u e)) (x (v e)) = xor (t (u e)) (t (v e))) ∧
      (∀ r ∈ R, keep r → x r = t r) := by
  constructor
  · intro h
    exact ⟨fun e hu hv => by rw [h _ hu, h _ hv], fun r _ hr => h r hr⟩
  · rintro ⟨hedge, hpin⟩ a ha
    obtain ⟨r, hr, hkeep, hpath⟩ := hR a ha
    exact eqAlong u v hedge hpath (hpin r hr hkeep)

end Prefix

section Partition

variable {A E : Type*} [Fintype A] [Fintype E]

noncomputable def markedPartition (w : E → Bool → ℤ) (δ : A → E → Bool)
    (marked : E → Bool) : ℤ[X] :=
  ∑ x : A, ∏ e : E,
    C (w e (δ x e)) * X^(if marked e && δ x e then 1 else 0)

theorem markedPartition_eval (w : E → Bool → ℤ) (δ : A → E → Bool)
    (marked : E → Bool) (z : ℤ) :
    (markedPartition w δ marked).eval z =
      ∑ x : A, ∏ e : E, w e (δ x e) * (if marked e && δ x e then z else 1) := by
  simp only [markedPartition, Polynomial.eval_finsetSum, Polynomial.eval_prod,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.prod_congr rfl
  intro e _
  split_ifs <;> simp

theorem markedPartition_degree (w : E → Bool → ℤ) (δ : A → E → Bool)
    (marked : E → Bool) : (markedPartition w δ marked).natDegree ≤ Fintype.card E := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro x _
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  calc
    _ ≤ ∑ _ : E, 1 := Finset.sum_le_sum ?_
    _ = Fintype.card E := by simp
  intro e _
  refine (Polynomial.natDegree_mul_le ..).trans ?_
  simp only [Polynomial.natDegree_C, zero_add, Polynomial.natDegree_pow,
    Polynomial.natDegree_X, mul_one]
  split_ifs <;> omega

theorem signedPartition_queries (w : E → Bool → ℤ) (δ : A → E → Bool)
    (marked : E → Bool) :
    let M := Fintype.card E
    (∑ x : A, ∏ e : E, w e (δ x e) * (if marked e && δ x e then -1 else 1)) =
      -((-1 : ℤ)^(M+1) * ∑ j ∈ range (M+1),
        ((-1 : ℤ)^(M-j) * ((M+1).choose (j+1) : ℤ)) *
        ∑ x : A, ∏ e : E, w e (δ x e) * (if marked e && δ x e then (j : ℤ) else 1)) := by
  dsimp only
  simpa only [markedPartition_eval] using
    eval_neg_one (markedPartition w δ marked) (Fintype.card E) (markedPartition_degree w δ marked)

end Partition

section WeightedPins

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

theorem weighted_pin_expansion (F : (V → Bool) → ℤ) (pins : Finset V) (p : V → Bool) :
    (2 : ℤ)^pins.card * (∑ x : V → Bool, if ∀ a ∈ pins, x a = p a then F x else 0) =
      ∑ S ∈ pins.powerset, (∏ a ∈ S, spinSign (p a)) *
        ∑ x : V → Bool, F x * ∏ a ∈ S, spinSign (x a) := by
  classical
  rw [Finset.mul_sum]
  calc
    _ = ∑ x : V → Bool, F x *
        ∑ S ∈ pins.powerset, ∏ a ∈ S, spinSign (x a) * spinSign (p a) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [pin_expansion]
      split_ifs <;> ring
    _ = _ := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro S _
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.prod_mul_distrib]
      ring

theorem pinnedPartition_queries (u v : E → V) (root : V)
    (connected : ∀ a, Relation.ReflTransGen (Adj u v) root a) (pins : Finset V) :
    ∃ masks : Finset V → E → Bool, ∀ (p : V → Bool) (w : E → Bool → ℤ),
      let M := Fintype.card E
      let δ := fun (x : V → Bool) (e : E) => xor (x (u e)) (x (v e))
      (2 : ℤ)^pins.card *
        (∑ x : V → Bool, if ∀ a ∈ pins, x a = p a then ∏ e : E, w e (δ x e) else 0) =
        ∑ S ∈ pins.powerset, if Even S.card then
          (∏ a ∈ S, spinSign (p a)) * (-((-1 : ℤ)^(M+1) * ∑ j ∈ range (M+1),
            ((-1 : ℤ)^(M-j) * ((M+1).choose (j+1) : ℤ)) *
            ∑ x : V → Bool, ∏ e : E, w e (δ x e) * (if masks S e && δ x e then (j : ℤ) else 1)))
          else 0 := by
  classical
  have hex (S : Finset V) : ∃ mask : E → Bool, Even S.card →
      ∀ x : V → Bool, (∏ a ∈ S, spinSign (x a)) =
        ∏ e : E, if mask e && xor (x (u e)) (x (v e)) then -1 else 1 := by
    by_cases h : Even S.card
    · obtain ⟨mask, hm⟩ := even_character u v root connected S h
      exact ⟨mask, fun _ => hm⟩
    · exact ⟨fun _ => false, fun hs => (h hs).elim⟩
  choose mask hmask using hex
  refine ⟨mask, fun p w => ?_⟩
  dsimp only
  rw [weighted_pin_expansion]
  apply Finset.sum_congr rfl
  intro S _
  split_ifs with h
  · congr 1
    rw [← signedPartition_queries]
    apply Finset.sum_congr rfl
    intro x _
    rw [hmask S h x, Finset.prod_mul_distrib]
  · rw [odd_character_sum S (Nat.not_even_iff_odd.mp h), mul_zero]
    intro x
    simp only [complement_disagreement]

end WeightedPins

theorem digits_eval (base : ℕ) (hb : 0 < base) (digits : List ℕ)
    (hd : ∀ a ∈ digits, a < base) (k : ℕ) (hk : k < digits.length) :
    Nat.ofDigits base digits / base^k % base = digits[k] := by
  rw [Nat.ofDigits_div_pow_eq_ofDigits_drop k hb digits hd, Nat.ofDigits_mod_eq_head!]
  have hhead : (digits.drop k).head! = digits[k] := by simp [List.head!_eq_getElem!, hk]
  rw [hhead, Nat.mod_eq_of_lt (hd _ (List.getElem_mem hk))]

theorem marked_query_width (n m f b : ℕ) :
    let H := n+m+f+b+2
    let d := n+m*b+1
    b + d*(m+1)^2 + (m+n) < H^4 := by
  dsimp only
  let K := n+m+f+b+1
  have hK : 1 ≤ K := by dsimp [K]; omega
  have hK0 : 0 < K := by omega
  have hm : m+1 ≤ K := by dsimp [K]; omega
  have hmb : m*b ≤ m*K := Nat.mul_le_mul_left _ (by dsimp [K]; omega)
  have hrest : n+1 ≤ (K-m)*K := by
    calc
      n+1 ≤ K-m := by dsimp [K]; omega
      _ = (K-m)*1 := by simp
      _ ≤ (K-m)*K := Nat.mul_le_mul_left _ hK
  have hd : n+m*b+1 ≤ K^2 := by
    calc
      n+m*b+1 ≤ (K-m)*K + m*K := by omega
      _ = K^2 := by rw [← add_mul, Nat.sub_add_cancel (show m ≤ K by omega), pow_two]
  have hmain : (n+m*b+1)*(m+1)^2 ≤ K^4 := by
    calc
      _ ≤ K^2 * K^2 := Nat.mul_le_mul hd (Nat.pow_le_pow_left hm 2)
      _ = K^4 := by ring
  have hbb : b + (m+n) + 1 ≤ K := by dsimp [K]; omega
  change b + (n + m * b + 1) * (m + 1) ^ 2 + (m + n) < (K+1)^4
  nlinarith [Nat.zero_le (K^3), Nat.zero_le (K^2)]

theorem query_factor_lt (n m f b : ℕ) (c : Fin 3) (w z : ℕ)
    (hw : w < 2^b) (hz : z ≤ m+n) :
    w * (2^(n+m*b+1))^((m+1)^c.val) * z < 2^(n+m+f+b+2)^4 := by
  have hc : (m+1)^c.val ≤ (m+1)^2 := Nat.pow_le_pow_right (by omega) (by omega)
  have hz' : z ≤ 2^(m+n) := hz.trans (Nat.le_of_lt (Nat.lt_two_pow_self))
  calc
    _ ≤ (2^b * (2^(n+m*b+1))^((m+1)^c.val)) * 2^(m+n) :=
      Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.le_of_lt hw)) hz'
    _ = 2^(b+(n+m*b+1)*(m+1)^c.val+(m+n)) := by rw [← pow_mul, ← pow_add, ← pow_add]
    _ < _ := Nat.pow_lt_pow_right (by decide) <|
      lt_of_le_of_lt (Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_left _ hc) _) _)
        (marked_query_width n m f b)

section Packed

variable {A : Type*} [Fintype A]

def bucket {K : ℕ} (label : A → Fin K) (weight : A → ℕ) (i : Fin K) : ℕ :=
  ∑ a ∈ Finset.univ.filter (fun a => label a = i), weight a

theorem bucket_lt {K R : ℕ} (label : A → Fin K) (weight : A → ℕ)
    (bound : ∑ a, weight a < R) (i : Fin K) : bucket label weight i < R :=
  (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset ..) (fun _ _ _ => Nat.zero_le _)).trans_lt bound

theorem pack_buckets {K : ℕ} (R : ℕ) (label : A → Fin K) (weight : A → ℕ) :
    (∑ a : A, weight a * R^(label a).val) =
      Nat.ofDigits R (List.ofFn (bucket label weight)) := by
  have hm : List.mapIdx (fun i a => a * R^i) (List.ofFn (bucket label weight)) =
      List.ofFn (fun i : Fin K => bucket label weight i * R^i.val) := by
    ext i; simp
  rw [Nat.ofDigits_eq_sum_mapIdx, hm, List.sum_ofFn]
  symm
  rw [← Finset.sum_fiberwise Finset.univ label (fun a => weight a * R^(label a).val)]
  apply Finset.sum_congr rfl
  intro i _
  rw [bucket, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  rw [(Finset.mem_filter.mp ha).2]

theorem bin_of_pack {K d : ℕ} (label : A → Fin K) (weight : A → ℕ)
    (bound : ∑ a, weight a < 2^d) (i : Fin K) (j : Fin d) :
    (∑ a : A, weight a * (2^d)^(label a).val).testBit (d*i.val+j.val) =
      (bucket label weight i).testBit j.val := by
  rw [pack_buckets]
  let digits := List.ofFn (bucket label weight)
  have hlt : ∀ a ∈ digits, a < 2^d := by
    intro a ha
    obtain ⟨l, rfl⟩ := List.mem_ofFn.mp ha
    exact bucket_lt label weight bound l
  have h := digits_eval (2^d) (by positivity) digits hlt i.val (by simp [digits])
  simp only [digits, List.getElem_ofFn] at h
  rw [← h, Nat.testBit_mod_two_pow, ← pow_mul, Nat.testBit_div_two_pow]
  simp only [j.isLt, decide_true, Bool.true_and, add_comm j.val]

end Packed

section Selection

variable {N : ℕ}

def below (weight : Fin N → ℕ) (x : ℕ) : ℕ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin N => i.val < x), weight i

def intervalWeight (weight : Fin N → ℕ) (lo hi : ℕ) : ℕ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin N => lo ≤ i.val ∧ i.val < hi), weight i

theorem below_interval (weight : Fin N → ℕ) {lo hi : ℕ} (h : lo ≤ hi) :
    below weight lo + intervalWeight weight lo hi = below weight hi := by
  classical
  unfold below intervalWeight
  rw [← Finset.sum_union]
  · congr 1
    ext i
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  · rw [Finset.disjoint_left]
    intro i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega

theorem interval_digit (weight : Fin N → ℕ) {lo p : ℕ} (hp : 0 < p) :
    intervalWeight weight (lo*p) ((lo+1)*p) =
      ∑ i ∈ Finset.univ.filter (fun i : Fin N => i.val/p = lo), weight i := by
  unfold intervalWeight
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [← Nat.le_div_iff_mul_le hp, ← Nat.div_lt_iff_lt_mul hp]
  omega

theorem select_step (weight : Fin N → ℕ) {lo mid hi index lower : ℕ}
    (hlm : lo ≤ mid) (_hmh : mid ≤ hi) (hlow : lower = below weight lo)
    (hidxlo : lower ≤ index) (hidxhi : index < below weight hi) :
    let left := lower + intervalWeight weight lo mid
    let right := decide (left ≤ index)
    let lo' := if right then mid else lo
    let hi' := if right then hi else mid
    let lower' := if right then left else lower
    lower' = below weight lo' ∧ lower' ≤ index ∧ index < below weight hi' := by
  have hmid : lower + intervalWeight weight lo mid = below weight mid := by
    rw [hlow, below_interval weight hlm]
  dsimp only
  by_cases h : lower + intervalWeight weight lo mid ≤ index
  · rw [decide_eq_true h]
    exact ⟨hmid, h, hidxhi⟩
  · rw [decide_eq_false h]
    exact ⟨hlow, hidxlo, hmid ▸ Nat.lt_of_not_ge h⟩

theorem interval_to_witness (weight : Fin N → ℕ) {p index : ℕ} (hp : p < N)
    (hlo : below weight p ≤ index) (hhi : index < below weight (p+1)) :
    ∃ x : Fin N, x.val = p ∧
      (∑ y ∈ Finset.univ.filter (fun y : Fin N => y < x), weight y) ≤ index ∧
      index < (∑ y ∈ Finset.univ.filter (fun y : Fin N => y ≤ x), weight y) := by
  refine ⟨⟨p, hp⟩, rfl, hlo, ?_⟩
  have hf : Finset.univ.filter (fun y : Fin N => y ≤ ⟨p, hp⟩) =
      Finset.univ.filter (fun y : Fin N => y.val < p+1) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_def]
    omega
  rw [hf]
  exact hhi

end Selection

section AugmentedGraph

variable {V E G : Type*}

def augmentedU (u : E → V) : E ⊕ V → V ⊕ G :=
  Sum.elim (Sum.inl ∘ u) Sum.inl

def augmentedV (v : E → V) (face : V → Option G) : E ⊕ V → V ⊕ G :=
  Sum.elim (Sum.inl ∘ v) (fun a => (face a).elim (Sum.inl a) Sum.inr)

theorem augmented_connected (u v : E → V) (face : V → Option G) (root : V)
    (connected : ∀ a, Relation.ReflTransGen (Adj u v) root a)
    (surj : ∀ g, ∃ a, face a = some g) :
    ∀ a : V ⊕ G, Relation.ReflTransGen (Adj (augmentedU u) (augmentedV v face)) (.inl root) a := by
  have hl (a : V) : Relation.ReflTransGen (Adj (augmentedU u) (augmentedV v face)) (.inl root) (.inl a) := by
    induction connected a with
    | refl => exact .refl
    | tail _ h ih =>
      obtain ⟨e, he⟩ := h
      apply ih.tail
      refine ⟨.inl e, ?_⟩
      simpa [augmentedU, augmentedV] using he
  intro a
  cases a with
  | inl a => exact hl a
  | inr g =>
    obtain ⟨vtx, hv⟩ := surj g
    exact (hl vtx).tail ⟨.inr vtx, Or.inl ⟨rfl, by simp [augmentedV, hv]⟩⟩

section GhostPins

variable [Fintype G] [DecidableEq V] [DecidableEq G]

def pinset (R : Finset V) : Finset (V ⊕ G) :=
  R.map ⟨Sum.inl, Sum.inl_injective⟩ ∪ (Finset.univ : Finset G).map ⟨Sum.inr, Sum.inr_injective⟩

theorem pinset_card (R : Finset V) :
    (pinset (G := G) R).card = R.card + Fintype.card G := by
  classical
  rw [pinset, Finset.card_union_of_disjoint]
  · simp
  · simp [Finset.disjoint_left]

theorem pinset_condition (R : Finset V) (x : V ⊕ G → Bool) (target : V → Bool) :
    (∀ v ∈ pinset R, x v = Sum.elim target (fun _ : G => false) v) ↔
      (∀ v ∈ R, x (.inl v) = target v) ∧ (∀ g : G, x (.inr g) = false) := by
  classical
  simp [pinset, Finset.mem_union, or_imp, forall_and]

theorem ghost_fixed_sum [Fintype V] (W : (V ⊕ G → Bool) → ℕ) (P : (V → Bool) → Prop)
    [DecidablePred P] :
    (∑ x : V ⊕ G → Bool, if P (x ∘ Sum.inl) ∧ (∀ g : G, x (.inr g) = false)
      then W x else 0) =
      ∑ z : V → Bool, if P z then W (Sum.elim z (fun _ : G => false)) else 0 := by
  classical
  let e : ((V ⊕ G) → Bool) ≃ ((V → Bool) × (G → Bool)) := Equiv.sumArrowEquivProdArrow V G Bool
  convert (Fintype.sum_equiv e _ (fun a : (V → Bool) × (G → Bool) =>
    if P a.1 ∧ a.2 = (fun _ => false) then W (Sum.elim a.1 a.2) else 0) ?_).trans ?_
  · intro x
    simp only [e, Equiv.sumArrowEquivProdArrow]
    have hc : (∀ g : G, x (.inr g) = false) ↔ x ∘ Sum.inr = (fun _ => false) := by
      rw [funext_iff]
      rfl
    have he : Sum.elim (x ∘ Sum.inl) (x ∘ Sum.inr) = x := by
      funext a
      cases a <;> rfl
    simp [hc, he]
  · rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro z _
    rw [Finset.sum_eq_single (fun _ : G => false)]
    · simp
    · intro q _ hq
      simp [hq]
    · simp

end GhostPins

end AugmentedGraph

theorem tally_power {E C : Type*} [Fintype E] [Fintype C] [DecidableEq C]
    (delta : E → Bool) (color : E → C) (radix : ℕ) (digit : C → ℕ) :
    (∏ e : E, if delta e then radix^(digit (color e)) else 1) =
      radix^(∑ j : C, (Finset.univ.filter (fun e : E => color e = j ∧ delta e = true)).card * digit j) := by
  classical
  have h (e : E) : (if delta e then radix^(digit (color e)) else 1) =
      radix^(if delta e then digit (color e) else 0) := by split_ifs <;> simp
  simp_rw [h, Finset.prod_pow_eq_pow_sum]
  congr 1
  rw [← Finset.sum_fiberwise Finset.univ color (fun e => if delta e then digit (color e) else 0)]
  apply Finset.sum_congr rfl
  intro j _
  have hs : (∑ e ∈ Finset.univ.filter (fun e => color e = j), if delta e then digit (color e) else 0) =
      ∑ e ∈ Finset.univ.filter (fun e => color e = j), if delta e then digit j else 0 := by
    apply Finset.sum_congr rfl
    intro e he
    rw [(Finset.mem_filter.mp he).2]
  rw [hs, ← Finset.sum_filter, Finset.filter_filter, Finset.sum_const, nsmul_eq_mul]
  rfl

def tripleCode {k : ℕ} (a b c : Fin k) : Fin ((k*k)*k) :=
  finProdFinEquiv (finProdFinEquiv (c,b),a)

theorem tripleCode_val {k : ℕ} (a b c : Fin k) :
    (tripleCode a b c).val = a.val + b.val*k + c.val*k^2 := by
  change a.val+k*(b.val+k*c.val) = _
  ring

theorem tripleCode_eq {k : ℕ} {a b c a' b' c' : Fin k} :
    tripleCode a b c = tripleCode a' b' c' ↔ a = a' ∧ b = b' ∧ c = c' := by
  simp only [tripleCode, Equiv.apply_eq_iff_eq, Prod.mk.injEq]
  tauto

def tallyFin {m : ℕ} (color : Fin m → Fin 3) (delta : Fin m → Bool) (j : Fin 3) :
    Fin (m+1) :=
  ⟨(Finset.univ.filter (fun e => color e = j ∧ delta e = true)).card,
    Nat.lt_succ_of_le (by
      simpa using Finset.card_filter_le (Finset.univ : Finset (Fin m))
        (fun e => color e = j ∧ delta e = true))⟩

theorem tallyFin_code {m rad : ℕ} (color : Fin m → Fin 3) (delta : Fin m → Bool) :
    (∏ e, if delta e then rad^((m+1)^(color e).val) else 1) =
      rad^(tripleCode (tallyFin color delta 0) (tallyFin color delta 1) (tallyFin color delta 2)).val := by
  rw [tally_power delta color rad (fun j => (m+1)^j.val), tripleCode_val, Fin.sum_univ_three]
  simp [tallyFin]

theorem weight_total_lt {n m b : ℕ}
    (w : Fin m → Bool → Fin (2^b))
    (delta : Fin (2^n) → Fin m → Bool)
    (permit : Fin (2^n) → Prop) [DecidablePred permit] :
    (∑ x, if permit x then ∏ e, (w e (delta x e)).val else 0) < 2^(n+m*b+1) := by
  calc
    _ ≤ ∑ _ : Fin (2^n), 2^(m*b) := by
      apply Finset.sum_le_sum
      intro x _
      split_ifs
      · calc
          _ ≤ ∏ _ : Fin m, 2^b := Finset.prod_le_prod (fun e _ => Nat.le_of_lt (w e (delta x e)).isLt)
          _ = 2^(m*b) := by simp [← pow_mul, Nat.mul_comm]
      · exact Nat.zero_le _
    _ = 2^(n+m*b) := by simp [← pow_add]
    _ < _ := Nat.pow_lt_pow_right (by decide) (by omega)

def msbSpin {n : ℕ} (x : Fin (2^n)) (i : Fin n) : Bool := x.val.testBit (n-1-i.val)

theorem prefixDiv_eq_iff {n q : ℕ} (hq : q ≤ n) (x y : Fin (2^n)) :
    x.val / 2^(n-q) = y.val / 2^(n-q) ↔
      ∀ i : Fin n, i.val < q → msbSpin x i = msbSpin y i := by
  constructor
  · intro h i hi
    have hbit := congrArg (fun z : ℕ => z.testBit (q-1-i.val)) h
    simp only [Nat.testBit_div_two_pow] at hbit
    have hind : q-1-i.val+(n-q) = n-1-i.val := by omega
    rw [hind] at hbit
    exact hbit
  · intro h
    apply Nat.eq_of_testBit_eq
    intro j
    simp only [Nat.testBit_div_two_pow]
    by_cases hj : j < q
    · let i : Fin n := ⟨q-1-j, by omega⟩
      have hs := h i (by dsimp [i]; omega)
      have hi : n-1-i.val = j+(n-q) := by dsimp [i]; omega
      simpa only [msbSpin, hi] using hs
    · have hge : n ≤ j+(n-q) := by omega
      have hm := Nat.pow_le_pow_right (by decide : 0 < 2) hge
      rw [Nat.testBit_eq_false_of_lt (x.isLt.trans_le hm),
        Nat.testBit_eq_false_of_lt (y.isLt.trans_le hm)]

section PinnedMass

variable {V E G : Type*} [Fintype V] [Fintype E] [Fintype G]
    [DecidableEq V] [DecidableEq G]

def coverWeights (face : V → Option G) (w : E → Bool → ℕ) (permit : V → Bool → Bool) :
    (E ⊕ V) → Bool → ℕ
  | .inl e, bit => w e bit
  | .inr i, bit => if (face i).isSome then (permit i bit).toNat else 1

def forceEdges (u v : E → V) (keep target : V → Bool) (w : E → Bool → ℕ)
    (e : E) (bit : Bool) : ℕ :=
  if keep (u e) = true ∧ keep (v e) = true ∧ bit ≠ xor (target (u e)) (target (v e))
  then 0 else w e bit

omit [Fintype V] [DecidableEq V] in
theorem prod_forceEdges (u v : E → V) (keep target : V → Bool) (w : E → Bool → ℕ)
    (x : V → Bool) :
    (∏ e, forceEdges u v keep target w e (xor (x (u e)) (x (v e)))) =
      if ∀ e, keep (u e) = true → keep (v e) = true →
        xor (x (u e)) (x (v e)) = xor (target (u e)) (target (v e))
      then ∏ e, w e (xor (x (u e)) (x (v e))) else 0 := by
  classical
  split_ifs with h
  · apply Finset.prod_congr rfl
    intro e _
    unfold forceEdges
    apply ite_eq_right
    rintro ⟨hu, hv, hn⟩
    exact hn (h e hu hv)
  · push Not at h
    obtain ⟨e, h₁, h₂, h₃⟩ := h
    exact Finset.prod_eq_zero (Finset.mem_univ e) (ite_eq_left ⟨h₁,h₂,h₃⟩)

omit [Fintype G] [DecidableEq V] [DecidableEq G] in
theorem prod_permissions (face : V → Option G) (permit : V → Bool → Bool)
    (x : V → Bool) :
    (∏ i : V, if (face i).isSome then (permit i (x i)).toNat else 1) =
      if ∀ i : V, (face i).isSome = true → permit i (x i) = true then 1 else 0 := by
  classical
  split_ifs with h
  · apply Finset.prod_eq_one
    intro i _
    by_cases hi : (face i).isSome = true <;> simp [hi, h i]
  · push Not at h
    obtain ⟨i, h₁, h₂⟩ := h
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    simp [h₁, Bool.eq_false_iff.mpr h₂]

omit [Fintype G] [DecidableEq V] [DecidableEq G] in
theorem coverWeights_fixed (u v : E → V) (face : V → Option G) (w : E → Bool → ℕ)
    (permit : V → Bool → Bool) (x : V → Bool) :
    let xg := Sum.elim x (fun _ : G => false)
    (∏ e : E ⊕ V, coverWeights face w permit e
        (xor (xg (augmentedU u e)) (xg (augmentedV v face e)))) =
      (∏ e : E, w e (xor (x (u e)) (x (v e)))) *
        (if ∀ i : V, (face i).isSome = true → permit i (x i) = true then 1 else 0) := by
  classical
  dsimp only
  rw [Fintype.prod_sum_type, ← prod_permissions face permit x]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  cases hf : face i <;> simp [coverWeights, augmentedU, augmentedV, hf]

theorem guarded_product (P Q S : Prop) [Decidable P] [Decidable Q] [Decidable S] (a : ℕ) :
    (if P then (if Q then a else 0) * (if S then 1 else 0) else 0) =
      if (Q ∧ P) ∧ S then a else 0 := by
  by_cases hp : P <;> by_cases hq : Q <;> by_cases hs : S <;> simp [hp, hq, hs]

theorem constrained_mass (u v : E → V) (face : V → Option G) (w : E → Bool → ℕ)
    (permit : V → Bool → Bool) (keep target : V → Bool) (R : Finset V)
    (hreps : ∀ a, keep a = true → ∃ r ∈ R, keep r = true ∧
      Relation.ReflTransGen (fun i j => keep i = true ∧ keep j = true ∧ Adj u v i j) a r) :
    (∑ x : V ⊕ G → Bool,
      if ∀ a ∈ pinset (R.filter fun r => keep r = true),
        x a = Sum.elim target (fun _ : G => false) a then
        ∏ e : E ⊕ V, coverWeights face (forceEdges u v keep target w) permit e
          (xor (x (augmentedU u e)) (x (augmentedV v face e)))
      else 0) =
    ∑ x : V → Bool,
      if (∀ i, keep i = true → x i = target i) ∧
        (∀ i, (face i).isSome = true → permit i (x i) = true) then
        ∏ e : E, w e (xor (x (u e)) (x (v e)))
      else 0 := by
  classical
  simp_rw [pinset_condition]
  have hf := ghost_fixed_sum (fun x : V ⊕ G → Bool =>
    ∏ e : E ⊕ V, coverWeights face (forceEdges u v keep target w) permit e
      (xor (x (augmentedU u e)) (x (augmentedV v face e))))
    (fun x => ∀ r ∈ R.filter (fun r => keep r = true), x r = target r)
  simp only [Function.comp_apply] at hf
  rw [hf]
  apply Finset.sum_congr rfl
  intro x _
  simp only [coverWeights_fixed, prod_forceEdges, Finset.mem_filter, and_imp]
  simp only [prefix_constraints u v hreps]
  exact guarded_product _ _ _ _

end PinnedMass

end PEqualNP.Outside.L_pcx_436_aux
namespace PEqualNP.Outside.L_pcx_436_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open scoped BigOperators

def inputBits (d x : ℕ) : List Bool := List.ofFn fun j : Fin d => x.testBit j.val

def weightsList {l : ℕ} (B : ℕ) (w : Fin l → Bool → Fin (2^B)) : List Bool :=
  (List.ofFn fun e => inputBits B (w e false).val ++ inputBits B (w e true).val).flatten

def oracleArguments {l B : ℕ} (hB : 0 < B) (w : Fin l → Bool → Fin (2^B)) :
    Fin (2+2*l*B) → Bool :=
  fun j => Fin.append (![false,true] : Fin 2 → Bool)
    (encodeBlocks (show 0 < B+B by omega) (edgeWord w)) ⟨j.val, by have := j.isLt; nlinarith⟩

theorem oracleArguments_ofFn {l B : ℕ} (hB : 0 < B) (w : Fin l → Bool → Fin (2^B)) :
    List.ofFn (oracleArguments hB w) = [false,true] ++ weightsList B w := by
  unfold oracleArguments
  have hz : 2+2*l*B = 2+l*(B+B) := by ring
  change List.ofFn (fun j =>
    Fin.append (![false,true] : Fin 2 → Bool) (encodeBlocks _ (edgeWord w)) (Fin.cast hz j)) = _
  rw [← List.ofFn_congr hz.symm, List.ofFn_fin_append, encodeBlocks_ofFn]
  simp only [edgeWord_ofFn]
  rfl

def zeroField {n m f B : ℕ} (u v : Fin m → Fin n) (face : Fin n → Option (Fin f))
    (w : Fin (m+n) → Bool → Fin (2^B)) : ℕ :=
  ∑ x : Fin n → Bool, ∑ y : Fin f → Bool,
    (∏ e : Fin m, (w (Fin.castAdd n e) (xor (x (u e)) (x (v e)))).val) *
      ∏ i : Fin n, (face i).elim 1 (fun j => (w (Fin.natAdd m i) (xor (x i) (y j))).val)

theorem HasCirc.queryWords {n m f B D s r X : ℕ} (hB : 0 < B) (hr : 0 < r)
    {u v : Fin m → Fin n} {face : Fin n → Option (Fin f)}
    {g : Circuit} {out : Fin D → Fin (2+2*(m+n)*B+g.size)}
    (hv : ReadsBack (2+2*(m+n)*B) g)
    (hvg : ∀ g' ∈ g.gates, ValidGate g') (hs : g.size ≤ s)
    (hev : ∀ w : Fin (m+n) → Bool → Fin (2^B),
      bitsToNat (fun j => (g.wires ([false,true] ++ weightsList B w)).getD (out j).val false) =
        zeroField u v face w)
    {wf : (Fin r → Bool) → Fin (m+n) → Bool → Fin (2^B)}
    (hW : ∀ e k, HasCirc r B X (fun x => natToBits B (wf x e k).val)) :
    HasCirc r D (4+(m+n)*(X+X)+s)
      (fun x => natToBits D (zeroField u v face (wf x))) := by
  have hE (e : Fin (m+n)) :
      HasCirc r (B+B) (X+X) (fun x => edgeWord (wf x) e) :=
    HasCirc.pair (hW e false) (hW e true)
  have hp := HasCirc.encodeWords (by omega) hE
  have hc₀ := HasCirc.const hr false
  have hc₁ := HasCirc.const hr true
  have h2 : HasCirc r 2 4 (fun _ => ![false,true]) := by
    apply (HasCirc.pair hc₀ hc₁).congr
    intro x j
    fin_cases j <;> rfl
  have hinput := HasCirc.pair h2 hp
  have hraw := HasCirc.fromCircuit g out hv hvg hs
  have heq : 2+2*(m+n)*B = 2+(m+n)*(B+B) := by ring
  have hresult := HasCirc.comp hinput (hraw.reindex (Fin.cast heq))
  refine hresult.congr ?_
  intro x j
  change (g.wires (List.ofFn (oracleArguments hB (wf x)))).getD (out j).val false = _
  rw [oracleArguments_ofFn, ← hev, natToBits_bitsToNat]

theorem HasCirc.zeroExtend {n a w A : ℕ} (hn : 0 < n)
    {f : (Fin n → Bool) → Fin a → Bool} (hf : HasCirc n a A f) :
    HasCirc n w (A+2) (fun x => natToBits w (bitsToNat (f x))) := by
  let idx (j : Fin w) : Fin (a+1) :=
    if h : j.val < a then Fin.castAdd 1 ⟨j.val,h⟩ else Fin.natAdd a 0
  refine ((HasCirc.pair hf (HasCirc.const hn false)).outputs idx).congr ?_
  intro x j
  by_cases h : j.val < a
  · simp only [idx, dite_eq_left h, Fin.append_left]
    exact congrFun (natToBits_bitsToNat (f x)).symm ⟨j.val,h⟩
  · simp only [idx, dite_eq_right h, Fin.append_right]
    exact (Nat.testBit_eq_false_of_lt ((bitsToNat_lt (f x)).trans_le
      (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_gt h)))).symm

end PEqualNP.Outside.L_pcx_436_aux
namespace PEqualNP.Outside.L_pcx_436_aux

open scoped BigOperators

def markerExponent {m : ℕ} (d : ℕ) (color : Fin m → Fin 3) (e : Fin m) (k : Bool) : ℕ :=
  if k then d*(m+1)^(color e).val else 0

def physicalMarked {m : ℕ} (d : ℕ) (color : Fin m → Fin 3)
    (w : Fin m → Bool → ℕ) (e : Fin m) (k : Bool) : ℕ :=
  w e k * 2^(markerExponent d color e k)

def interpolationFactor {n m : ℕ} (mask : (Fin m ⊕ Fin n) → Bool)
    (t : Fin (m+n+1)) (e : Fin m ⊕ Fin n) (k : Bool) : ℕ :=
  if mask e && k then t.val else 1

def packedQueryWeight {n m f : ℕ} (d : ℕ) (u v : Fin m → Fin n) (color : Fin m → Fin 3)
    (face : Fin n → Option (Fin f)) (keep target : Fin n → Bool)
    (w : Fin m → Bool → ℕ) (p : Fin n → Bool → Bool)
    (mask : (Fin m ⊕ Fin n) → Bool) (t : Fin (m+n+1)) (e : Fin m ⊕ Fin n) (k : Bool) : ℕ :=
  coverWeights face (forceEdges u v keep target (physicalMarked d color w)) p e k *
    interpolationFactor mask t e k

theorem interpolationFactor_le {n m : ℕ} (hn : 0 < n) (mask : (Fin m ⊕ Fin n) → Bool)
    (t : Fin (m+n+1)) (e : Fin m ⊕ Fin n) (k : Bool) :
    interpolationFactor mask t e k ≤ m+n := by
  unfold interpolationFactor
  split_ifs <;> have := t.isLt <;> omega

theorem packedQueryWeight_lt {n m f b : ℕ} (hn : 0 < n)
    (u v : Fin m → Fin n) (color : Fin m → Fin 3) (face : Fin n → Option (Fin f))
    (keep target : Fin n → Bool) (w : Fin m → Bool → Fin (2^b)) (p : Fin n → Bool → Bool)
    (mask : (Fin m ⊕ Fin n) → Bool) (t : Fin (m+n+1)) (e : Fin m ⊕ Fin n) (k : Bool) :
    packedQueryWeight (n+m*b+1) u v color face keep target (fun e b => (w e b).val)
      p mask t e k < 2^(n+m+f+b+2)^4 := by
  have hcoef := interpolationFactor_le hn mask t e k
  cases e with
  | inl e =>
    simp only [packedQueryWeight, coverWeights, forceEdges]
    split_ifs with h
    · simp
    · unfold physicalMarked
      have he : markerExponent (n+m*b+1) color e k ≤ (n+m*b+1)*(m+1)^(color e).val := by
        cases k <;> simp [markerExponent]
      refine (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) he))).trans_lt ?_
      rw [pow_mul]
      exact query_factor_lt n m f b (color e) _ _ (w e k).isLt hcoef
  | inr i =>
    have hbase : coverWeights face (forceEdges u v keep target (physicalMarked (n+m*b+1) color
        (fun e b => (w e b).val))) p (Sum.inr i) k ≤ 1 := by
      simp only [coverWeights]
      cases p i k <;> split_ifs <;> decide
    have hM : m+n ≤ (n+m+f+b+2)^4 := by
      have h : n+m+f+b+2 ≤ (n+m+f+b+2)^4 := Nat.le_pow (by decide)
      omega
    unfold packedQueryWeight
    refine (Nat.mul_le_mul hbase hcoef).trans_lt ?_
    rw [one_mul]
    exact hM.trans_lt Nat.lt_two_pow_self

theorem HasCirc.markedPhys {N n m b B d T : ℕ} (hN : 0 < N) (hB : 0 < B)
    {u v : Fin m → Fin n} {color : Fin m → Fin 3} {keep : Fin n → Bool}
    {spin : (Fin N → Bool) → Fin n → Bool} {w : (Fin N → Bool) → Fin m → Bool → Fin (2^b)}
    (hspin : ∀ i, HasCirc N 1 T (fun x _ => spin x i))
    (hw : ∀ e k, HasCirc N b T (fun x => natToBits b (w x e k).val))
    (width coeff : ℕ) (hc : coeff < 2^width) (e : Fin m) (k : Bool) :
    HasCirc N B (3*T+width*(18*B+4)+8*B+14)
      (fun x => natToBits B (forceEdges u v keep (spin x)
        (physicalMarked d color (fun e k => (w x e k).val)) e k * coeff)) := by
  have hW : HasCirc N B (T+2) (fun x => natToBits B (w x e k).val) := by
    refine ((hw e k).zeroExtend hN).congr ?_
    intro x j
    rw [bitsToNat_natToBits (w x e k).isLt]
  have hscaled : HasCirc N B (T+2+(2*B+width*(18*B+4)))
      (fun x => natToBits B ((w x e k).val * coeff)) := by
    refine (HasCirc.comp hW (HasCirc.scale B width coeff hB hc)).congr ?_
    intro x j
    rw [bitsToNat_truncate]
    have hM : (((w x e k).val % 2^B) * coeff) % 2^B = ((w x e k).val * coeff) % 2^B := by
      conv_lhs => rw [Nat.mul_mod]
      rw [Nat.mod_mod, ← Nat.mul_mod]
    rw [← natToBits_mod, hM, natToBits_mod]
  let shift := markerExponent d color e k
  have hval : HasCirc N B (T+2+(2*B+width*(18*B+4))+2)
      (fun x => natToBits B ((w x e k).val * 2^shift * coeff)) := by
    refine (HasCirc.shiftLeft hN shift hscaled).congr ?_
    intro x j
    rw [shiftBits, mul_right_comm]
  by_cases h : keep (u e) = true ∧ keep (v e) = true
  · have hx := HasCirc.xor2 (hspin (u e)) (hspin (v e))
    have hmatch : HasCirc N 1 (T+T+6)
        (fun x _ => decide (k = xor (spin x (u e)) (spin x (v e)))) := by
      cases k
      · refine (HasCirc.not1 hx).weaken (by omega) |>.congr ?_
        intro x j
        cases xor (spin x (u e)) (spin x (v e)) <;> rfl
      · refine hx.weaken (by omega) |>.congr ?_
        intro x j
        cases xor (spin x (u e)) (spin x (v e)) <;> rfl
    refine ((HasCirc.muxWords hmatch hval (HasCirc.constBits hN 0)).weaken (by omega)).congr ?_
    intro x j
    unfold forceEdges physicalMarked
    by_cases hk : k = xor (spin x (u e)) (spin x (v e))
    · have hk' : ¬ (keep (u e) = true ∧ keep (v e) = true ∧
          k ≠ xor (spin x (u e)) (spin x (v e))) := fun hh => hh.2.2 hk
      rw [ite_eq_left (decide_eq_true hk), ite_eq_right hk']
    · have hk' : keep (u e) = true ∧ keep (v e) = true ∧
          k ≠ xor (spin x (u e)) (spin x (v e)) := ⟨h.1,h.2,hk⟩
      have hk'' : decide (k = xor (spin x (u e)) (spin x (v e))) ≠ true := by
        rw [decide_eq_false hk]
        decide
      rw [ite_eq_right hk'', ite_eq_left hk', zero_mul]
  · refine hval.weaken (by omega) |>.congr ?_
    intro x j
    have h' : ¬ (keep (u e) = true ∧ keep (v e) = true ∧ k ≠ xor (spin x (u e)) (spin x (v e))) :=
      fun hh => h ⟨hh.1,hh.2.1⟩
    simp only [forceEdges, h', ite_false, physicalMarked, shift]

theorem HasCirc.markedGhost {N n f B T : ℕ} (hN : 0 < N)
    {face : Fin n → Option (Fin f)} {p : (Fin N → Bool) → Fin n → Bool → Bool}
    (hp : ∀ i k, HasCirc N 1 T (fun x _ => p x i k)) (i : Fin n) (k : Bool) (coeff : ℕ) :
    HasCirc N B (T+8*B) (fun x =>
      natToBits B ((if (face i).isSome then (p x i k).toNat else 1) * coeff)) := by
  by_cases h : (face i).isSome = true
  · refine ((HasCirc.muxWords (hp i k) (HasCirc.constBits (B := B) hN coeff) (HasCirc.constBits hN 0)).weaken (by omega)).congr ?_
    intro x j
    cases he : p x i k <;> simp [*]
  · refine (HasCirc.constBits hN coeff).weaken (by omega) |>.congr ?_
    intro x j
    simp [h]

end PEqualNP.Outside.L_pcx_436_aux
namespace PEqualNP.Outside.L_pcx_436_aux

open scoped BigOperators

def spinParity (xs : List Bool) : Bool := xs.foldr xor false

theorem spinParity_sign (xs : List Bool) :
    spinSign (spinParity xs) = (xs.map spinSign).prod := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    change spinSign (xor a (spinParity xs)) = spinSign a * (xs.map spinSign).prod
    rw [spinSign_xor, ih]

noncomputable def pinParity {V : Type*} (S : Finset V) (p : V → Bool) : Bool :=
  spinParity (S.toList.map p)

theorem pinParity_sign {V : Type*} (S : Finset V) (p : V → Bool) :
    spinSign (pinParity S p) = ∏ v ∈ S, spinSign (p v) := by
  rw [pinParity, spinParity_sign, List.map_map, Finset.prod_map_toList]
  rfl

def interpolationNeg (M j : ℕ) : Bool := !(decide (Even ((M+1)+(M-j)+1)))

theorem interpolationNeg_sign (M j : ℕ) :
    spinSign (interpolationNeg M j) = -((-1 : ℤ)^(M+1) * (-1)^(M-j)) := by
  rw [← pow_add, ← mul_neg_one, ← pow_succ]
  by_cases h : Even ((M+1)+(M-j)+1)
  · rw [h.neg_one_pow]
    simp [interpolationNeg, spinSign, h]
  · rw [(Nat.not_even_iff_odd.mp h).neg_one_pow]
    simp [interpolationNeg, spinSign, h]

def packedPrefix {n m f : ℕ} (d : ℕ) (u v : Fin m → Fin n) (color : Fin m → Fin 3)
    (face : Fin n → Option (Fin f)) (keep target : Fin n → Bool)
    (w : Fin m → Bool → ℕ) (p : Fin n → Bool → Bool) : ℕ :=
  ∑ x : Fin n → Bool,
    if (∀ i, keep i = true → x i = target i) ∧
      (∀ i, (face i).isSome = true → p i (x i) = true) then
      ∏ e : Fin m, physicalMarked d color w e (xor (x (u e)) (x (v e)))
    else 0

def augmentedPartition {n m f : ℕ} (u v : Fin m → Fin n) (face : Fin n → Option (Fin f))
    (q : (Fin m ⊕ Fin n) → Bool → ℕ) : ℕ :=
  ∑ x : Fin n ⊕ Fin f → Bool,
    ∏ e : Fin m ⊕ Fin n, q e (xor (x (augmentedU u e)) (x (augmentedV v face e)))

theorem zeroField_augmented {n m f B : ℕ} (u v : Fin m → Fin n) (face : Fin n → Option (Fin f))
    (q : Fin (m+n) → Bool → Fin (2^B))
    (hq : ∀ i, face i = none → (q (Fin.natAdd m i) false).val = 1) :
    zeroField u v face q = augmentedPartition u v face (fun e k => (q (finSumFinEquiv e) k).val) := by
  classical
  unfold zeroField augmentedPartition
  let summand (xy : (Fin n → Bool) × (Fin f → Bool)) :=
    (∏ e : Fin m, (q (Fin.castAdd n e) (xor (xy.1 (u e)) (xy.1 (v e)))).val) *
      ∏ i : Fin n, (face i).elim 1 (fun j => (q (Fin.natAdd m i) (xor (xy.1 i) (xy.2 j))).val)
  change (∑ x : Fin n → Bool, ∑ y : Fin f → Bool, summand (x,y)) = _
  rw [← Fintype.sum_prod_type summand]
  let e := (Equiv.sumArrowEquivProdArrow (Fin n) (Fin f) Bool).symm
  refine Fintype.sum_equiv e _ _ fun x => ?_
  change _ = ∏ e : Fin m ⊕ Fin n, (q (finSumFinEquiv e) (xor
    (Sum.elim x.1 x.2 (augmentedU u e)) (Sum.elim x.1 x.2 (augmentedV v face e)))).val
  rw [Fintype.prod_sum_type]
  dsimp only [summand]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  cases hc : face i
  · simp [augmentedU, augmentedV, hc, hq i hc]
  · simp [augmentedU, augmentedV, hc]

theorem spinSign_action (b : Bool) (x : ℤ) :
    spinSign b * x = if b then -x else x := by
  cases b <;> simp [spinSign]

theorem pinnedQueryFormula {n m f d : ℕ} (u v : Fin m → Fin n) (color : Fin m → Fin 3)
    (face : Fin n → Option (Fin f)) (root : Fin n)
    (hconn : ∀ a, Relation.ReflTransGen (Adj u v) root a) (hface : ∀ g, ∃ a, face a = some g)
    (keep : Fin n → Bool) (R : Finset (Fin n))
    (hreps : ∀ a, keep a = true → ∃ r ∈ R, keep r = true ∧
      Relation.ReflTransGen (fun i j => keep i = true ∧ keep j = true ∧ Adj u v i j) a r) :
    ∃ masks : Finset (Fin n ⊕ Fin f) → (Fin m ⊕ Fin n) → Bool,
    let pins := pinset (G := Fin f) (R.filter fun r => keep r = true)
    ∀ (target : Fin n → Bool) (w : Fin m → Bool → ℕ) (p : Fin n → Bool → Bool),
      (2 : ℤ)^pins.card * (packedPrefix d u v color face keep target w p : ℤ) =
        ∑ S ∈ pins.powerset, ∑ j : Fin (m+n+1),
          if Even S.card then
            let neg := xor (pinParity S (Sum.elim target (fun _ => false))) (interpolationNeg (m+n) j.val)
            let a := (m+n+1).choose (j.val+1)
            let z := augmentedPartition u v face (packedQueryWeight d u v color face keep target w p (masks S) j)
            if neg then -((a : ℤ)*(z : ℤ)) else (a : ℤ)*(z : ℤ)
          else 0 := by
  classical
  let pins := pinset (G := Fin f) (R.filter fun r => keep r = true)
  obtain ⟨mask, hm⟩ := pinnedPartition_queries (augmentedU u) (augmentedV v face) (.inl root)
    (augmented_connected u v face root hconn hface) pins
  refine ⟨mask, ?_⟩
  dsimp only
  intro target w p
  let base := coverWeights face (forceEdges u v keep target (physicalMarked d color w)) p
  specialize hm (Sum.elim target (fun _ => false)) (fun e b => (base e b : ℤ))
  dsimp only at hm
  simp only [Fintype.card_sum, Fintype.card_fin] at hm
  have hmass := constrained_mass u v face (physicalMarked d color w) p keep target R hreps
  have hmass' :
      (∑ x : Fin n ⊕ Fin f → Bool, if ∀ a ∈ pins, x a = Sum.elim target (fun _ => false) a then
        ∏ e : Fin m ⊕ Fin n, ((base e (xor (x (augmentedU u e)) (x (augmentedV v face e))) : ℕ) : ℤ) else 0)
      = (packedPrefix d u v color face keep target w p : ℤ) := by
    have hv := congrArg (fun x : ℕ => (x : ℤ)) hmass
    push_cast at hv
    unfold packedPrefix
    push_cast
    simpa only [pins, base] using hv
  rw [← hmass', hm]
  apply Finset.sum_congr rfl
  intro S _
  by_cases hS : Even S.card
  · simp only [hS, ite_true]
    rw [← Fin.sum_univ_eq_sum_range]
    rw [← neg_mul, ← mul_assoc]
    nth_rw 1 [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [← spinSign_action, spinSign_xor, pinParity_sign, interpolationNeg_sign]
    have hQ :
        (∑ x : Fin n ⊕ Fin f → Bool,
          ∏ e : Fin m ⊕ Fin n, (base e (xor (x (augmentedU u e)) (x (augmentedV v face e))) : ℤ) *
            (if mask S e && xor (x (augmentedU u e)) (x (augmentedV v face e)) then (j.val : ℤ) else 1)) =
          (augmentedPartition u v face (packedQueryWeight d u v color face keep target w p (mask S) j) : ℤ) := by
      unfold augmentedPartition packedQueryWeight interpolationFactor
      push_cast
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.prod_congr rfl
      intro e _
      split_ifs <;> rfl
    rw [hQ]
    ring
  · simp [hS]

end PEqualNP.Outside.L_pcx_436_aux
namespace PEqualNP.Outside.L_pcx_436_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open scoped BigOperators

def intResidue (w : ℕ) (z : ℤ) : ℕ := (z % ((2^w : ℕ) : ℤ)).toNat

theorem intResidue_lt (w : ℕ) (z : ℤ) : intResidue w z < 2^w := by
  unfold intResidue
  have hpos : (0 : ℤ) < (2^w : ℕ) := by positivity
  have hne : ((2^w : ℕ) : ℤ) ≠ 0 := ne_of_gt hpos
  exact_mod_cast (Int.toNat_of_nonneg (Int.emod_nonneg z hne)).trans_lt (Int.emod_lt_of_pos z hpos)

theorem intResidue_cast (w : ℕ) (z : ℤ) :
    (intResidue w z : ℤ) = z % ((2^w : ℕ) : ℤ) := by
  apply Int.toNat_of_nonneg
  exact Int.emod_nonneg _ (by positivity)

theorem intResidue_nat (w x : ℕ) : intResidue w x = x % 2^w := by
  rw [intResidue, ← Int.natCast_mod, Int.toNat_natCast]

theorem intResidue_add (w : ℕ) (x y : ℤ) :
    (intResidue w x + intResidue w y) % 2^w = intResidue w (x+y) := by
  apply Int.ofNat_inj.mp
  simp only [Int.natCast_mod, Int.natCast_add, intResidue_cast]
  exact (Int.add_emod x y _).symm

theorem intResidue_neg (w : ℕ) (x : ℤ) :
    (2^w - intResidue w x) % 2^w = intResidue w (-x) := by
  apply Int.ofNat_inj.mp
  rw [Int.natCast_mod, Int.natCast_sub (Nat.le_of_lt (intResidue_lt w x)), intResidue_cast,
    intResidue_cast]
  have h := Int.sub_emod ((2^w : ℕ) : ℤ) x ((2^w : ℕ) : ℤ)
  simpa using h.symm

theorem intResidue_sum {ι : Type*} (s : Finset ι) (w : ℕ) (f : ι → ℤ) :
    (∑ i ∈ s, intResidue w (f i)) % 2^w = intResidue w (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [intResidue]
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj, Nat.add_mod, ih,
      Nat.mod_eq_of_lt (intResidue_lt w (f j)), intResidue_add]

theorem HasCirc.sumInt {n w k B : ℕ} (hn : 0 < n) (hw : 0 < w)
    {f : Fin k → (Fin n → Bool) → ℤ}
    (hf : ∀ i, HasCirc n w B (fun x => natToBits w (intResidue w (f i x)))) :
    HasCirc n w (2*w+k*(B+(16*w+2))) (fun x =>
      natToBits w (intResidue w (∑ i : Fin k, f i x))) := by
  refine (HasCirc.sumWords hn hw hf).congr ?_
  intro x j
  simp_rw [bitsToNat_natToBits (intResidue_lt w _)]
  rw [← natToBits_mod, intResidue_sum]

theorem HasCirc.signedScale {n w A B : ℕ} (hn : 0 < n) (hw : 0 < w)
    (k coeff : ℕ) (hcoeff : coeff < 2^k)
    {f : (Fin n → Bool) → Fin w → Bool} {neg : (Fin n → Bool) → Fin 1 → Bool}
    (hf : HasCirc n w A f) (hneg : HasCirc n 1 B neg) :
    HasCirc n w (B + ((2*w + (A+(2*w+k*(18*w+4))) + (16*w+w+5)) +
      (A+(2*w+k*(18*w+4)))) + 4*w)
      (fun x => natToBits w (intResidue w
        (if neg x 0 then -(coeff * (bitsToNat (f x) : ℤ)) else coeff * (bitsToNat (f x) : ℤ)))) := by
  have hp0 := HasCirc.comp hf (HasCirc.scale w k coeff hw hcoeff)
  have hp : HasCirc n w (A+(2*w+k*(18*w+4)))
      (fun x => natToBits w (intResidue w (coeff * (bitsToNat (f x) : ℤ)))) := by
    apply hp0.congr
    intro x i
    have hcast : (coeff : ℤ) * (bitsToNat (f x) : ℤ) =
        ((bitsToNat (f x)*coeff : ℕ) : ℤ) := by push_cast; ring
    rw [hcast, intResidue_nat, natToBits_mod]
  have hm := HasCirc.subWrapWords hw (HasCirc.constBits (B := w) hn 0) hp
  refine (HasCirc.muxWords hneg hm hp).congr ?_
  intro x i
  by_cases h : neg x 0 = true
  · rw [ite_eq_left h, ite_eq_left h, bitsToNat_natToBits (by positivity : 0 < 2^w),
      bitsToNat_natToBits (intResidue_lt w _), add_zero, ← natToBits_mod, intResidue_neg]
  · rw [ite_eq_right h, ite_eq_right h]

end PEqualNP.Outside.L_pcx_436_aux
namespace PEqualNP.Outside.L_pcx_436_aux

open scoped BigOperators

theorem HasCirc.parity {N T : ℕ} (hN : 0 < N) {I : Type*} (l : List I)
    {v : (Fin N → Bool) → I → Bool}
    (hv : ∀ i, HasCirc N 1 T (fun x _ => v x i)) :
    HasCirc N 1 (2+l.length*(T+4)) (fun x _ => spinParity (l.map (v x))) := by
  induction l with
  | nil => simpa [spinParity] using HasCirc.const hN false
  | cons i l ih =>
    have hh := HasCirc.xor2 (hv i) ih
    refine hh.weaken ?_ |>.congr ?_
    · simp only [List.length_cons, Nat.add_mul, one_mul]
      omega
    · intro x j
      rfl

theorem HasCirc.recoverPacked {N W L k K B : ℕ} (hN : 0 < N) (hW : 0 < W)
    (hL : k+L ≤ W) {terms : Fin K → (Fin N → Bool) → ℤ} {P : (Fin N → Bool) → ℕ}
    (hterms : ∀ i, HasCirc N W B (fun x => natToBits W (intResidue W (terms i x))))
    (hcorrect : ∀ x, (∑ i, terms i x) = ((P x * 2^k : ℕ) : ℤ))
    (hbound : ∀ x, P x < 2^L) :
    HasCirc N L (2*W+K*(B+(16*W+2))) (fun x => natToBits L (P x)) := by
  let idx (j : Fin L) : Fin W := ⟨j.val+k, by omega⟩
  refine ((HasCirc.sumInt hN hW hterms).outputs idx).congr ?_
  intro x j
  have hpos : 0 < 2^k := by positivity
  have hb : P x * 2^k < 2^W := by
    calc
      _ < 2^L * 2^k := Nat.mul_lt_mul_of_pos_right (hbound x) hpos
      _ = 2^(L+k) := by rw [pow_add]
      _ ≤ 2^W := Nat.pow_le_pow_right (by decide) (by omega)
  rw [hcorrect, intResidue_nat, Nat.mod_eq_of_lt hb]
  change (P x * 2^k).testBit (j.val+k) = (P x).testBit j.val
  rw [← Nat.testBit_div_two_pow, Nat.mul_div_cancel _ hpos]

theorem spinCard_pins {n f : ℕ} (R : Finset (Fin n)) (keep : Fin n → Bool) (c : ℕ)
    (hR : R.card ≤ c) :
    (pinset (G := Fin f) (R.filter fun i => keep i = true)).card ≤ f+c := by
  rw [pinset_card, Fintype.card_fin]
  have hh := Finset.card_filter_le R (fun i => keep i = true)
  omega

theorem HasCirc.writeBit {N L A B : ℕ} {old : (Fin N → Bool) → Fin L → Bool}
    {bit : (Fin N → Bool) → Fin 1 → Bool}
    (hOld : HasCirc N L A old) (hBit : HasCirc N 1 B bit) (i : Fin L) :
    HasCirc N L (A+B) (fun x j => if j = i then bit x 0 else old x j) := by
  let idx (j : Fin L) : Fin (L+1) :=
    if j = i then Fin.natAdd L 0 else Fin.castAdd 1 j
  refine ((HasCirc.pair hOld hBit).outputs idx).congr ?_
  intro x j
  by_cases h : j=i <;> simp only [idx, h, ite_true, ite_false, Fin.append_left, Fin.append_right]

end PEqualNP.Outside.L_pcx_436_aux

namespace PEqualNP.Outside.L_pcx_436_aux

open scoped BigOperators

theorem msbSpin_rev {n : ℕ} (x : Fin (2^n)) (i : Fin n) :
    msbSpin x i = natToBits n x.val i.rev := by
  simp only [msbSpin, natToBits, Fin.val_rev]
  congr 1
  omega

def spinEquiv (n : ℕ) : Fin (2^n) ≃ (Fin n → Bool) where
  toFun := msbSpin
  invFun a := ⟨bitsToNat (fun i => a i.rev), bitsToNat_lt _⟩
  left_inv x := by
    apply Fin.ext
    change bitsToNat (fun i : Fin n => msbSpin x i.rev) = x.val
    simp_rw [msbSpin_rev, Fin.rev_rev]
    exact bitsToNat_natToBits x.isLt
  right_inv a := by
    funext i
    change msbSpin ⟨bitsToNat (fun j : Fin n => a j.rev), _⟩ i = a i
    rw [msbSpin_rev]
    have h := congrFun (natToBits_bitsToNat (fun j : Fin n => a j.rev)) i.rev
    simpa only [Fin.rev_rev] using h

theorem spinEquiv_weight {n : ℕ} (a : Fin n → Bool) :
    ((spinEquiv n).symm a).val = ∑ i : Fin n, (a i).toNat * 2^(n-1-i.val) := by
  change (∑ i : Fin n, (a i.rev).toNat * 2^i.val) = _
  refine Fintype.sum_equiv Fin.revPerm _ _ fun i => ?_
  change (a i.rev).toNat * 2^i.val = (a i.rev).toNat * 2^(n-1-i.rev.val)
  rw [← show i.rev.rev.val = n-1-i.rev.val by simp only [Fin.val_rev]; omega, Fin.rev_rev]

end PEqualNP.Outside.L_pcx_436_aux
namespace PEqualNP.Outside.L_pcx_436_aux

open scoped BigOperators

def spinDiff {n m : ℕ} (u v : Fin m → Fin n) (x : Fin (2^n)) (e : Fin m) : Bool :=
  xor (msbSpin x (u e)) (msbSpin x (v e))

def histogramLabel {n m : ℕ} (u v : Fin m → Fin n) (color : Fin m → Fin 3)
    (x : Fin (2^n)) : Fin (((m+1)*(m+1))*(m+1)) :=
  tripleCode (tallyFin color (spinDiff u v x) 0) (tallyFin color (spinDiff u v x) 1)
    (tallyFin color (spinDiff u v x) 2)

def prefixMass {n m f : ℕ} (u v : Fin m → Fin n) (face : Fin n → Option (Fin f))
    (keep target : Fin n → Bool) (w : Fin m → Bool → ℕ) (p : Fin n → Bool → Bool)
    (x : Fin (2^n)) : ℕ :=
  if (∀ i, keep i = true → msbSpin x i = target i) ∧
    (∀ i, (face i).isSome = true → p i (msbSpin x i) = true) then
    ∏ e : Fin m, w e (spinDiff u v x e) else 0

theorem packedPrefix_eq {n m f d : ℕ} (u v : Fin m → Fin n) (color : Fin m → Fin 3)
    (face : Fin n → Option (Fin f)) (keep target : Fin n → Bool)
    (w : Fin m → Bool → ℕ) (p : Fin n → Bool → Bool) :
    packedPrefix d u v color face keep target w p =
      ∑ x : Fin (2^n), prefixMass u v face keep target w p x * (2^d)^(histogramLabel u v color x).val := by
  unfold packedPrefix
  refine Fintype.sum_equiv (spinEquiv n).symm _ _ (fun a => ?_)
  let x := (spinEquiv n).symm a
  have h : msbSpin x = a := (spinEquiv n).apply_symm_apply _
  have hp : (∏ e : Fin m, physicalMarked d color w e (spinDiff u v x e)) =
      (∏ e : Fin m, w e (spinDiff u v x e)) * (2^d)^(histogramLabel u v color x).val := by
    unfold physicalMarked
    rw [Finset.prod_mul_distrib]
    congr 1
    rw [histogramLabel, ← tallyFin_code]
    apply Finset.prod_congr rfl
    intro e _
    unfold markerExponent
    cases spinDiff u v x e <;> simp [pow_mul]
  have hdelta : (fun e => xor (a (u e)) (a (v e))) = spinDiff u v x := by
    funext e
    simp [spinDiff, h]
  change (if (∀ i, keep i = true → a i = target i) ∧
    (∀ i, (face i).isSome = true → p i (a i) = true) then
    ∏ e, physicalMarked d color w e ((fun e => xor (a (u e)) (a (v e))) e) else 0) =
    prefixMass u v face keep target w p x * (2^d)^(histogramLabel u v color x).val
  rw [hdelta, hp, prefixMass, h]
  split_ifs <;> simp

theorem prefixMass_lt {n m f b : ℕ} (u v : Fin m → Fin n) (face : Fin n → Option (Fin f))
    (keep target : Fin n → Bool) (w : Fin m → Bool → Fin (2^b)) (p : Fin n → Bool → Bool) :
    (∑ x : Fin (2^n), prefixMass u v face keep target (fun e k => (w e k).val) p x) <
      2^(n+m*b+1) := by
  simpa only [prefixMass] using weight_total_lt w (spinDiff u v)
    (fun x => (∀ i, keep i = true → msbSpin x i = target i) ∧
      (∀ i, (face i).isSome = true → p i (msbSpin x i) = true))

theorem packedPrefix_lt {n m f b : ℕ} (u v : Fin m → Fin n) (color : Fin m → Fin 3)
    (face : Fin n → Option (Fin f)) (keep target : Fin n → Bool)
    (w : Fin m → Bool → Fin (2^b)) (p : Fin n → Bool → Bool) :
    packedPrefix (n+m*b+1) u v color face keep target (fun e k => (w e k).val) p <
      2^((n+m*b+1)*(((m+1)*(m+1))*(m+1))) := by
  let d := n+m*b+1
  let k := ((m+1)*(m+1))*(m+1)
  let l := histogramLabel u v color
  let W := prefixMass u v face keep target (fun e k => (w e k).val) p
  have hb := prefixMass_lt u v face keep target w p
  rw [packedPrefix_eq, pack_buckets, pow_mul]
  change Nat.ofDigits (2^d) (List.ofFn (bucket l W)) < (2^d)^k
  have hlt : ∀ a ∈ List.ofFn (bucket l W), a < 2^d := by
    intro a ha
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ha
    exact bucket_lt l W hb j
  have h2 : 1 < 2^d := by
    have hdp : 0 < d := by dsimp [d]; omega
    exact Nat.one_lt_two_pow hdp.ne'
  simpa only [List.length_ofFn] using Nat.ofDigits_lt_base_pow_length h2 hlt

theorem packedPrefix_bit {n m f b : ℕ} (u v : Fin m → Fin n) (color : Fin m → Fin 3)
    (face : Fin n → Option (Fin f)) (keep target : Fin n → Bool)
    (w : Fin m → Bool → Fin (2^b)) (p : Fin n → Bool → Bool)
    (i : Fin (((m+1)*(m+1))*(m+1))) (j : Fin (n+m*b+1)) :
    (packedPrefix (n+m*b+1) u v color face keep target (fun e k => (w e k).val) p).testBit
      ((n+m*b+1)*i.val+j.val) =
      (bucket (histogramLabel u v color)
        (prefixMass u v face keep target (fun e k => (w e k).val) p) i).testBit j.val := by
  rw [packedPrefix_eq]
  exact bin_of_pack _ _ (prefixMass_lt u v face keep target w p) i j

end PEqualNP.Outside.L_pcx_436_aux
namespace PEqualNP.Outside.L_pcx_436_aux

open scoped BigOperators
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

def inputWeightBudget (M B T : ℕ) : ℕ :=
  3*T+(M+1)*(18*B+4)+8*B+14

def termBudget (n m f B W s T : ℕ) : ℕ :=
  let X := inputWeightBudget (m+n) B T
  let Q := 4+(m+n)*(X+X)+s+2
  let P := 8+(n+f)*(T+6)
  let A := Q+(2*W+(m+n+2)*(18*W+4))
  P+(2*W+A+(17*W+5)+A)+4*W

theorem HasCirc.buildPackedPrefix {N n m f c b D s T : ℕ}
    (hN : 0 < N) (hn : 0 < n)
    (u v : Fin m → Fin n) (color : Fin m → Fin 3) (face : Fin n → Option (Fin f))
    (root : Fin n) (hconn : ∀ a, Relation.ReflTransGen (Adj u v) root a) (hface : ∀ g, ∃ a, face a = some g)
    (keep : Fin n → Bool) (R : Finset (Fin n)) (hR : R.card ≤ c)
    (hreps : ∀ a, keep a = true → ∃ r ∈ R, keep r = true ∧
      Relation.ReflTransGen (fun i j => keep i = true ∧ keep j = true ∧ Adj u v i j) a r)
    (spin : (Fin N → Bool) → Fin n → Bool) (w : (Fin N → Bool) → Fin m → Bool → Fin (2^b))
    (p : (Fin N → Bool) → Fin n → Bool → Bool)
    (hspin : ∀ i, HasCirc N 1 T (fun x _ => spin x i))
    (hw : ∀ e k, HasCirc N b T (fun x => natToBits b (w x e k).val))
    (hp : ∀ i k, HasCirc N 1 T (fun x _ => p x i k)) :
    let B := (n+m+f+b+2)^4
    let L := (n+m*b+1)*(((m+1)*(m+1))*(m+1))
    let W := L+(n+f)+D
    ∀ {g : Circuit} {out : Fin D → Fin (2+2*(m+n)*B+g.size)},
    ReadsBack (2+2*(m+n)*B) g → (∀ g' ∈ g.gates, ValidGate g') → g.size ≤ s →
    (∀ w' : Fin (m+n) → Bool → Fin (2^B),
      bitsToNat (fun j => (g.wires ([false,true] ++ weightsList B w')).getD (out j).val false) =
        zeroField u v face w') →
    HasCirc N L (2*W + ((m+n+1)*2^(f+c))*(termBudget n m f B W s T+(16*W+2)))
      (fun x => natToBits L (packedPrefix (n+m*b+1) u v color face keep (spin x)
        (fun e k => (w x e k).val) (p x))) := by
  classical
  intro B L W g out hG hlegal hsize heval
  let pins := pinset (G := Fin f) (R.filter fun i => keep i = true)
  let X := inputWeightBudget (m+n) B T
  have hB : 0 < B := by dsimp [B]; positivity
  have hL : 0 < L := by dsimp [L]; positivity
  have hW : 0 < W := by dsimp [W]; omega
  have hpins : pins.card ≤ n+f := by
    rw [pinset_card, Fintype.card_fin]
    have hle := Finset.card_le_univ (R.filter fun i => keep i = true)
    simpa [Nat.add_comm] using Nat.add_le_add_right hle f
  obtain ⟨masks, hformula⟩ := pinnedQueryFormula (d := n+m*b+1) u v color face root hconn hface keep R hreps
  let omegaType := ↥pins.powerset × Fin (m+n+1)
  let efin : Fin (Fintype.card omegaType) ≃ omegaType := (Fintype.equivFin omegaType).symm
  let target (x : Fin N → Bool) : Fin n ⊕ Fin f → Bool := Sum.elim (spin x) fun _ => false
  let Q (i : omegaType) (x : Fin N → Bool) : ℕ :=
    augmentedPartition u v face (packedQueryWeight (n+m*b+1) u v color face keep (spin x)
      (fun e k => (w x e k).val) (p x) (masks i.1.val) i.2)
  let neg (i : omegaType) (x : Fin N → Bool) : Bool :=
    xor (pinParity i.1.val (target x)) (interpolationNeg (m+n) i.2.val)
  let coef (i : omegaType) : ℕ := (m+n+1).choose (i.2.val+1)
  let term (i : omegaType) (x : Fin N → Bool) : ℤ :=
    if Even i.1.val.card then
      if neg i x then -((coef i : ℤ)*(Q i x : ℤ)) else (coef i : ℤ)*(Q i x : ℤ)
    else 0
  have hterms (i : omegaType) :
      HasCirc N W (termBudget n m f B W s T) (fun x => natToBits W (intResidue W (term i x))) := by
    by_cases heven : Even i.1.val.card
    · let mask := masks i.1.val
      let w' (x : Fin N → Bool) (e : Fin (m+n)) (k : Bool) : Fin (2^B) :=
        ⟨packedQueryWeight (n+m*b+1) u v color face keep (spin x) (fun e k => (w x e k).val)
          (p x) mask i.2 (finSumFinEquiv.symm e) k, packedQueryWeight_lt hn u v color face keep
            (spin x) (w x) (p x) mask i.2 (finSumFinEquiv.symm e) k⟩
      have hw' (e : Fin (m+n)) (k : Bool) : HasCirc N B X (fun x => natToBits B (w' x e k).val) := by
        generalize h : finSumFinEquiv.symm e = a
        let acoef := interpolationFactor mask i.2 a k
        have hcoeff : acoef < 2^(m+n+1) := by
          have hle := interpolationFactor_le hn mask i.2 a k
          exact hle.trans_lt ((Nat.lt_succ_self _).trans Nat.lt_two_pow_self)
        cases a with
        | inl j =>
          simpa only [w', h, packedQueryWeight, coverWeights, X, inputWeightBudget, acoef] using
            HasCirc.markedPhys (B := B) (d := n+m*b+1) (u := u) (v := v) (color := color) (keep := keep)
              hN hB hspin hw (m+n+1) acoef hcoeff j k
        | inr j =>
          have hb : T+8*B ≤ X := by unfold X inputWeightBudget; omega
          simpa only [w', h, packedQueryWeight, coverWeights, acoef] using
            (HasCirc.markedGhost (B := B) (face := face) hN hp j k acoef).weaken hb
      have hz (x : Fin N → Bool) : zeroField u v face (w' x) = Q i x := by
        rw [zeroField_augmented u v face (w' x) (by
          intro j hj
          simp [w', packedQueryWeight, coverWeights, interpolationFactor, hj])]
        unfold Q
        simp only [w', Equiv.symm_apply_apply]
        rfl
      have hQ0 := HasCirc.queryWords hB hN hG hlegal hsize heval hw'
      have hQ := hQ0.congr (fun x j => by rw [hz x])
      have hQlt (x : Fin N → Bool) : Q i x < 2^D :=
        (hz x) ▸ ((heval (w' x)) ▸ bitsToNat_lt _)
      have hQW := (hQ.zeroExtend (w := W) hN).congr (fun x j => by rw [bitsToNat_natToBits (hQlt x)])
      have ht (j : Fin n ⊕ Fin f) : HasCirc N 1 (T+2) (fun x _ => target x j) := by
        cases j with
        | inl j => exact (hspin j).weaken (by omega)
        | inr j => exact (HasCirc.const hN false).weaken (by omega)
      have hpar := HasCirc.parity hN i.1.val.toList ht
      have hpn := HasCirc.xor2 hpar (HasCirc.const hN (interpolationNeg (m+n) i.2.val))
      have hbound : i.1.val.card ≤ n+f := by
        have hcard := Finset.card_le_univ i.1.val
        simpa using hcard
      have hpn' : HasCirc N 1 (8+(n+f)*(T+6)) (fun x _ => neg i x) := by
        have hb := Nat.mul_le_mul_right (T+6) hbound
        exact (hpn.weaken (by simp only [Finset.length_toList, show T+2+4 = T+6 by omega]; omega)).congr (fun _ _ => rfl)
      have hcoef : coef i < 2^(m+n+2) :=
        (Nat.choose_le_two_pow _ _).trans_lt (Nat.pow_lt_pow_right (by decide) (by omega))
      have hf := HasCirc.signedScale hN hW (m+n+2) (coef i) hcoef hQW hpn'
      refine hf.weaken ?_ |>.congr ?_
      · unfold termBudget X inputWeightBudget
        dsimp only
        omega
      · intro x j
        have hWlt : Q i x < 2^W := (hQlt x).trans_le (Nat.pow_le_pow_right (by decide) (by dsimp [W]; omega))
        simp only [term, heven, ite_true, bitsToNat_natToBits hWlt]
    · refine (HasCirc.constBits (B := W) hN 0).weaken ?_ |>.congr ?_
      · unfold termBudget
        dsimp only
        omega
      · intro x j
        simp [term, heven, intResidue]
  have hsum (x : Fin N → Bool) :
      (∑ i, term (efin i) x) = ((packedPrefix (n+m*b+1) u v color face keep (spin x)
        (fun e k => (w x e k).val) (p x) * 2^pins.card : ℕ) : ℤ) := by
    rw [efin.sum_comp (fun i => term i x)]
    rw [Fintype.sum_prod_type (fun i => term i x)]
    push_cast
    rw [mul_comm]
    have hf := (hformula (spin x) (fun e k => (w x e k).val) (p x)).symm
    rw [← Finset.sum_coe_sort pins.powerset] at hf
    exact hf
  have hrec := HasCirc.recoverPacked hN hW (by dsimp [W]; omega : pins.card+L ≤ W)
    (fun i => hterms (efin i)) hsum
    (fun x => packedPrefix_lt u v color face keep (spin x) (w x) (p x))
  have hcount : Fintype.card omegaType ≤ (m+n+1)*2^(f+c) := by
    simp only [omegaType, Fintype.card_prod, Fintype.card_coe, Finset.card_powerset, Fintype.card_fin]
    rw [Nat.mul_comm]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (spinCard_pins R keep c hR))
  exact hrec.weaken (Nat.add_le_add_left (Nat.mul_le_mul_right _ hcount) _)

end PEqualNP.Outside.L_pcx_436_aux
namespace PEqualNP.Outside.L_pcx_436_aux

open scoped BigOperators

def leftTarget {n : ℕ} (q : Fin n) (code : Fin n → Bool) (i : Fin n) : Bool :=
  natToBits n (bitsToNat code * 2^(n-q.val)) i.rev

theorem leftTarget_interval {n : ℕ} (q : Fin n) (code : Fin n → Bool)
    (hc : bitsToNat code < 2^q.val) (x : Fin (2^n)) :
    (∀ i : Fin n, i.val < q.val + 1 → msbSpin x i = leftTarget q code i) ↔
      (bitsToNat code)*2^(n-q.val) ≤ x.val ∧
        x.val < (2*bitsToNat code+1)*2^(n-(q.val+1)) := by
  let A := bitsToNat code
  have hA : A * 2^(n-q.val) < 2^n := by
    calc
      _ < 2^q.val * 2^(n-q.val) := Nat.mul_lt_mul_of_pos_right hc (by positivity)
      _ = _ := by rw [← pow_add, Nat.add_sub_of_le q.isLt.le]
  let y : Fin (2^n) := ⟨A*2^(n-q.val), hA⟩
  have hs : msbSpin y = leftTarget q code := funext (msbSpin_rev y)
  rw [← hs, ← prefixDiv_eq_iff (show q.val+1 ≤ n from q.isLt)]
  let k := 2^(n-(q.val+1))
  have hk : 0 < k := by dsimp [k]; positivity
  have hk2 : 2^(n-q.val) = 2*k := by
    rw [show n-q.val = n-(q.val+1)+1 by omega, pow_succ, Nat.mul_comm]
  have hy : y.val / k = 2*A := by
    change A * 2^(n-q.val) / k = _
    rw [hk2, ← Nat.mul_assoc, Nat.mul_div_cancel _ hk, Nat.mul_comm]
  change (x.val / k = y.val / k) ↔ A * 2^(n-q.val) ≤ x.val ∧ x.val < (2*A+1)*k
  rw [hy, hk2, ← Nat.mul_assoc, Nat.mul_comm A 2, ← Nat.le_div_iff_mul_le hk,
    ← Nat.div_lt_iff_lt_mul hk]
  omega

def UnrankInv {n : ℕ} (W : Fin (2^n) → ℕ) (offset q code lower : ℕ) : Prop :=
  code < 2^q ∧
    lower = below W (code*2^(n-q)) ∧
    lower ≤ offset ∧ offset < below W ((code+1)*2^(n-q))

theorem UnrankInv.init {n : ℕ} {W : Fin (2^n) → ℕ} {offset : ℕ} (h : offset < ∑ x, W x) :
    UnrankInv W offset 0 0 0 := by
  unfold UnrankInv
  simpa [below, Finset.filter_true_of_mem (fun (i : Fin (2^n)) _ => i.isLt)] using h

theorem UnrankInv.step {n : ℕ} {W : Fin (2^n) → ℕ} {offset q code lower left : ℕ}
    (hq : q < n) (h : UnrankInv W offset q code lower)
    (hleft : left = intervalWeight W (code*2^(n-q)) ((2*code+1)*2^(n-(q+1)))) :
    let s := lower + left
    let b := decide (s ≤ offset)
    UnrankInv W offset (q+1) (2*code+b.toNat) (if b then s else lower) := by
  obtain ⟨hc, hl, hoff, hh⟩ := h
  let k := 2^(n-(q+1))
  have hk : 2^(n-q) = 2*k := by rw [show n-q = n-(q+1)+1 by omega, pow_succ, Nat.mul_comm]
  have hs₀ : code*2^(n-q) = (2*code)*k := by rw [hk]; ring
  have hs₁ : (code+1)*2^(n-q) = (2*code+2)*k := by rw [hk]; ring
  have h1 : (2*code)*k ≤ (2*code+1)*k := Nat.mul_le_mul_right _ (by omega)
  have h2 : (2*code+1)*k ≤ (2*code+2)*k := Nat.mul_le_mul_right _ (by omega)
  rw [hs₀] at hl
  rw [hs₁] at hh
  rw [hs₀] at hleft
  have he := select_step W h1 h2 hl hoff hh
  dsimp only at he ⊢
  rw [← hleft] at he
  unfold UnrankInv
  change (2*code+(decide (lower+left ≤ offset)).toNat < 2^(q+1)) ∧ _
  rw [pow_succ]
  by_cases he' : lower+left ≤ offset
  · have ht := decide_eq_true he'
    rw [ht] at he ⊢
    simp only [Bool.toNat_true, ite_true] at he ⊢
    exact ⟨by omega, he⟩
  · have hf := decide_eq_false he'
    rw [hf] at he ⊢
    simp only [Bool.toNat_false, Nat.add_zero, Bool.false_eq_true, ite_false] at he ⊢
    exact ⟨by omega, he⟩

theorem UnrankInv.step_no_overflow {n d : ℕ} {W : Fin (2^n) → ℕ} {offset q code lower left : ℕ}
    (hq : q < n) (h : UnrankInv W offset q code lower)
    (hleft : left = intervalWeight W (code*2^(n-q)) ((2*code+1)*2^(n-(q+1))))
    (hbound : ∑ x, W x < 2^d) : lower+left < 2^d := by
  let mid := (2*code+1)*2^(n-(q+1))
  have hlow : code*2^(n-q) ≤ mid := by
    dsimp [mid]
    rw [show n-q = n-(q+1)+1 by omega, pow_succ]
    calc
      code * (2^(n-(q+1))*2) = (2*code)*2^(n-(q+1)) := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
  have hb : lower + left = below W mid := by
    rw [h.2.1, hleft]
    exact below_interval W hlow
  rw [hb]
  unfold below
  exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset ..)
    (fun _ _ _ => Nat.zero_le _)).trans_lt hbound

theorem UnrankInv.finish {n : ℕ} {W : Fin (2^n) → ℕ} {offset code lower : ℕ}
    (h : UnrankInv W offset n code lower) :
    ∃ x : Fin (2^n), x.val = code ∧
      (∑ y ∈ Finset.univ.filter (fun y : Fin (2^n) => y < x), W y) ≤ offset ∧
      offset < (∑ y ∈ Finset.univ.filter (fun y : Fin (2^n) => y ≤ x), W y) := by
  obtain ⟨hc, hl, hoff, hh⟩ := h
  simp only [Nat.sub_self, pow_zero, mul_one] at hl hh
  exact interval_to_witness _ hc (hl ▸ hoff) hh

end PEqualNP.Outside.L_pcx_436_aux
namespace PEqualNP.Outside.L_pcx_436_aux

open scoped BigOperators

theorem HasCirc.anyOf {N T : ℕ} (hN : 0 < N) {I : Type*} (l : List I)
    {f : (Fin N → Bool) → I → Bool} (hf : ∀ i, HasCirc N 1 T (fun x _ => f x i)) :
    HasCirc N 1 (2+l.length*(T+1)) (fun x _ => l.any (f x)) := by
  induction l with
  | nil => simpa using HasCirc.const hN false
  | cons i l ih =>
    refine (HasCirc.or2 (hf i) ih).weaken ?_ |>.congr ?_
    · simp only [List.length_cons, Nat.add_mul, one_mul]
      omega
    · intro x j
      rfl

def cellBit {K d : ℕ} (i : Fin K) (j : Fin d) : Fin (d*K) :=
  ⟨d*i.val+j.val, by
    have hi := Nat.mul_le_mul_left d (Nat.succ_le_of_lt i.isLt)
    change d*(i.val+1) ≤ d*K at hi
    rw [Nat.mul_add, Nat.mul_one] at hi
    simpa using lt_of_lt_of_le (Nat.add_lt_add_left j.isLt (d*i.val)) hi⟩

def readCell {K d : ℕ} (pick : Fin K → Bool) (hist : Fin (d*K) → Bool) (j : Fin d) : Bool :=
  (List.finRange K).any fun i => pick i && hist (cellBit i j)

theorem readCell_single {K d : ℕ} (k : Fin K) {pick : Fin K → Bool} {hist : Fin (d*K) → Bool}
    (hs : ∀ i, pick i = decide (i=k)) (j : Fin d) :
    readCell pick hist j = hist (cellBit k j) := by
  unfold readCell
  simp_rw [hs]
  cases hb : hist (cellBit k j)
  · apply Bool.eq_false_iff.mpr
    intro h
    rw [List.any_eq_true] at h
    obtain ⟨i, hi, h⟩ := h
    rw [Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨rfl, h⟩
    simp [hb] at h
  · rw [List.any_eq_true]
    exact ⟨k, List.mem_finRange _, by simp [hb]⟩

theorem HasCirc.addressed {N K d U V : ℕ} (hN : 0 < N)
    {sel : (Fin N → Bool) → Fin K → Bool} {hist : (Fin N → Bool) → Fin (d*K) → Bool}
    (hs : ∀ i, HasCirc N 1 U (fun x _ => sel x i)) (hh : HasCirc N (d*K) V hist) :
    HasCirc N d (V+d*(2+K*(U+2))) (fun x => readCell (sel x) (hist x)) := by
  have hpair := HasCirc.pair (HasCirc.proj (id : Fin N → Fin N)) hh
  let pick (x : Fin (N+d*K) → Bool) (i : Fin K) := sel (fun j : Fin N => x (j.castAdd (d*K))) i
  let score (x : Fin (N+d*K) → Bool) (i : Fin K) (j : Fin d) :=
    x ((cellBit i j).natAdd N)
  have hx (i : Fin K) (j : Fin d) :
      HasCirc (N+d*K) 1 (U+1) (fun x _ => pick x i && score x i j) := by
    exact (HasCirc.and2 ((hs i).reindex (Fin.castAdd (d*K)))
      (HasCirc.proj (fun _ : Fin 1 => (cellBit i j).natAdd N))).weaken (by omega)
  have hor (j : Fin d) :
      HasCirc (N+d*K) 1 (2+K*(U+2)) (fun x _ => (List.finRange K).any (fun i => pick x i && score x i j)) := by
    simpa [Nat.add_assoc] using HasCirc.anyOf (by omega : 0 < N+d*K) (List.finRange K) (fun i => hx i j)
  have hvec := HasCirc.vecConst hor
  refine (HasCirc.comp hpair hvec).weaken (by omega) |>.congr ?_
  intro x j
  simp only [readCell, pick, score, Fin.append_left, Fin.append_right, id_eq]

theorem HasCirc.leftSpin {N n T : ℕ} (hN : 0 < N) (q : Fin n)
    {code : (Fin N → Bool) → Fin n → Bool} (hc : HasCirc N n T code) (i : Fin n) :
    HasCirc N 1 (T+2) (fun x _ => leftTarget q (code x) i) := by
  refine ((HasCirc.shiftLeft hN (n-q.val) hc).outputs (fun _ : Fin 1 => i.rev)).congr ?_
  intro x _
  unfold leftTarget
  rw [← shiftBits]
  simp_rw [natToBits_bitsToNat]

theorem stepBit {n : ℕ} (a : ℕ) (b : Bool) (i : Fin n) :
    (if i.val = 0 then b else (2*a).testBit i.val) =
      (2*a+b.toNat).testBit i.val := by
  have hb : b.toNat < 2 := by cases b <;> decide
  have hstep : (2*a+b.toNat)/2 = a := by
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt hb, zero_add]
  have hstep' : (2*a)/2 = a := by omega
  obtain ⟨i, hi⟩ := i
  cases i with
  | zero => cases b <;> simp [Nat.testBit_zero, Nat.add_mod]
  | succ i => simp [Nat.testBit_succ, hstep, hstep']

def unrankRound {n d : ℕ} (code : Fin n → Bool) (lower left index : Fin d → Bool) :
    Fin (n+d) → Bool :=
  let sum := bitsToNat lower + bitsToNat left
  let right := decide (sum % 2^d ≤ bitsToNat index)
  Fin.append (natToBits n (2*bitsToNat code+right.toNat))
    (if right then natToBits d sum else lower)

theorem HasCirc.unrankRound {N n d B : ℕ} (hN : 0 < N) (hn : 0 < n) (hd : 0 < d)
    {code : (Fin N → Bool) → Fin n → Bool} {lower left index : (Fin N → Bool) → Fin d → Bool}
    (hc : HasCirc N n 0 code) (hl : HasCirc N d 0 lower)
    (hL : HasCirc N d B left) (hi : HasCirc N d 0 index) :
    HasCirc N (n+d) (3*B+100*(d+1)) (fun x => unrankRound (code x) (lower x) (left x) (index x)) := by
  let sum (x : Fin N → Bool) := bitsToNat (lower x) + bitsToNat (left x)
  let right (x : Fin N → Bool) := decide (sum x % 2^d ≤ bitsToNat (index x))
  have hs : HasCirc N d (B+(16*d+2)) (fun x => natToBits d (sum x)) :=
    (HasCirc.addWords hd hl hL).weaken (by omega)
  have hr : HasCirc N 1 (B+33*d+7) (fun x _ => right x) := by
    refine (HasCirc.geWords hd hi hs).weaken (by omega) |>.congr ?_
    intro x _
    rw [bitsToNat_truncate]
  have hh : HasCirc N n 2 (fun x => natToBits n (2*bitsToNat (code x))) := by
    refine (HasCirc.shiftLeft hN 1 hc).congr ?_
    intro x j
    rw [Nat.mul_comm, ← pow_one 2, ← shiftBits, natToBits_bitsToNat]
  let low : Fin n := ⟨0,hn⟩
  have hc' : HasCirc N n (2+(B+33*d+7))
      (fun x => natToBits n (2*bitsToNat (code x)+(right x).toNat)) := by
    refine (HasCirc.writeBit hh hr low).congr ?_
    intro x j
    simpa only [Fin.ext_iff, low, natToBits] using stepBit (bitsToNat (code x)) (right x) j
  have hl' : HasCirc N d ((B+33*d+7)+(B+(16*d+2)+0)+4*d)
      (fun x j => if right x then natToBits d (sum x) j else lower x j) :=
    HasCirc.muxWords hr hs hl
  refine ((HasCirc.pair hc' hl').weaken (by omega)).congr ?_
  intro x j
  change Fin.append (natToBits n (2*bitsToNat (code x)+(right x).toNat))
      (fun i => if right x then natToBits d (sum x) i else lower x i) j =
    Fin.append (natToBits n (2*bitsToNat (code x)+(right x).toNat))
      (if right x then natToBits d (sum x) else lower x) j
  by_cases hr : right x = true
  · simp only [hr, ite_true]
  · have hf : right x = false := Bool.eq_false_iff.mpr hr
    simp only [hf, Bool.false_eq_true, ite_false]

end PEqualNP.Outside.L_pcx_436_aux
namespace PEqualNP.Outside.L_pcx_436_aux

open scoped BigOperators

def keyMass {n m f : ℕ} (u v : Fin m → Fin n) (color : Fin m → Fin 3) (face : Fin n → Option (Fin f))
    (w : Fin m → Bool → ℕ) (p : Fin n → Bool → Bool)
    (key : Fin (((m+1)*(m+1))*(m+1))) (x : Fin (2^n)) : ℕ :=
  if (∀ i, (face i).isSome = true → p i (msbSpin x i) = true) ∧ histogramLabel u v color x = key then
    ∏ e : Fin m, w e (spinDiff u v x e) else 0

theorem keyMass_lt {n m f b : ℕ} (u v : Fin m → Fin n) (color : Fin m → Fin 3) (face : Fin n → Option (Fin f))
    (w : Fin m → Bool → Fin (2^b)) (p : Fin n → Bool → Bool)
    (key : Fin (((m+1)*(m+1))*(m+1))) :
    (∑ x, keyMass u v color face (fun e k => (w e k).val) p key x) < 2^(n+m*b+1) := by
  simpa only [keyMass] using weight_total_lt w (spinDiff u v)
    (fun x => (∀ i, (face i).isSome = true → p i (msbSpin x i) = true) ∧ histogramLabel u v color x = key)

theorem bucket_guards (K U P : Prop) [Decidable K] [Decidable U] [Decidable P] (a : ℕ) :
    (if K then (if U ∧ P then a else 0) else 0) =
      (if U then (if P ∧ K then a else 0) else 0) := by
  by_cases hk : K <;> by_cases hu : U <;> by_cases hp : P <;> simp [hk,hu,hp]

theorem bucket_prefix {n m f : ℕ} (u v : Fin m → Fin n) (color : Fin m → Fin 3) (face : Fin n → Option (Fin f))
    (w : Fin m → Bool → ℕ) (p : Fin n → Bool → Bool) (keep target : Fin n → Bool)
    (key : Fin (((m+1)*(m+1))*(m+1))) :
    bucket (histogramLabel u v color) (prefixMass u v face keep target w p) key =
      ∑ x : Fin (2^n), if ∀ i, keep i = true → msbSpin x i = target i then
        keyMass u v color face w p key x else 0 := by
  unfold bucket
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x _
  unfold prefixMass keyMass
  exact bucket_guards _ _ _ _

theorem readInitial {n m f b : ℕ} (u v : Fin m → Fin n) (color : Fin m → Fin 3) (face : Fin n → Option (Fin f))
    (w : Fin m → Bool → Fin (2^b)) (p : Fin n → Bool → Bool) (target : Fin n → Bool)
    (key : Fin (((m+1)*(m+1))*(m+1))) (j : Fin (n+m*b+1)) :
    (packedPrefix (n+m*b+1) u v color face (fun _ => false) target (fun e k => (w e k).val) p).testBit
      (cellBit key j).val =
    (∑ x, keyMass u v color face (fun e k => (w e k).val) p key x).testBit j.val := by
  rw [cellBit, packedPrefix_bit, bucket_prefix]
  simp

theorem readLeft {n m f b : ℕ} (u v : Fin m → Fin n) (color : Fin m → Fin 3) (face : Fin n → Option (Fin f))
    (w : Fin m → Bool → Fin (2^b)) (p : Fin n → Bool → Bool)
    (key : Fin (((m+1)*(m+1))*(m+1))) (q : Fin n) (code : Fin n → Bool)
    (hc : bitsToNat code < 2^q.val) (j : Fin (n+m*b+1)) :
    (packedPrefix (n+m*b+1) u v color face (fun i => decide (i.val < q.val+1)) (leftTarget q code)
      (fun e k => (w e k).val) p).testBit (cellBit key j).val =
    (intervalWeight (keyMass u v color face (fun e k => (w e k).val) p key)
      (bitsToNat code*2^(n-q.val)) ((2*bitsToNat code+1)*2^(n-(q.val+1)))).testBit j.val := by
  rw [cellBit, packedPrefix_bit, bucket_prefix, intervalWeight, Finset.sum_filter]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  simp only [decide_eq_true_eq]
  simp only [leftTarget_interval q code hc x]

theorem invariant_fold {α : Type*} {n : ℕ} (step : Fin n → α → α) (start : α)
    (Inv : ℕ → α → Prop) (hs : Inv 0 start)
    (hh : ∀ (i : Fin n) (x : α), Inv i.val x → Inv (i.val+1) (step i x)) :
    Inv n ((List.finRange n).foldl (fun x i => step i x) start) := by
  have H (j : ℕ) (h : j ≤ n) :
      Inv j (((List.finRange j).map (Fin.castLE h)).foldl (fun x i => step i x) start) := by
    induction j with
    | zero => simpa using hs
    | succ j ih =>
      rw [List.finRange_succ_last, List.map_append, List.foldl_append, List.map_map, List.map_cons,
        List.map_nil, List.foldl_cons, List.foldl_nil]
      exact hh ⟨j, h⟩ _ (ih (by omega))
  simpa using H n (Nat.le_refl n)

theorem unrankRound_inv {n d : ℕ} {W : Fin (2^n) → ℕ}
    (q : Fin n) (code : Fin n → Bool) (lower left index : Fin d → Bool)
    (hiv : UnrankInv W (bitsToNat index) q.val (bitsToNat code) (bitsToNat lower))
    (hleft : bitsToNat left = intervalWeight W (bitsToNat code*2^(n-q.val))
      ((2*bitsToNat code+1)*2^(n-(q.val+1))))
    (hbound : (∑ x, W x) < 2^d) :
    let S := unrankRound code lower left index
    UnrankInv W (bitsToNat index) (q.val+1)
      (bitsToNat (fun i : Fin n => S (i.castAdd d)))
      (bitsToNat (fun i : Fin d => S (i.natAdd n))) := by
  dsimp only
  let s := bitsToNat lower + bitsToNat left
  have hsum : s < 2^d := UnrankInv.step_no_overflow q.isLt hiv hleft hbound
  simp only [unrankRound, Fin.append_left, Fin.append_right]
  change UnrankInv W (bitsToNat index) (q.val+1)
    (bitsToNat (natToBits n (2*bitsToNat code+(decide (s % 2^d ≤ bitsToNat index)).toNat)))
    (bitsToNat (if decide (s % 2^d ≤ bitsToNat index) then natToBits d s else lower))
  rw [Nat.mod_eq_of_lt hsum]
  let right := decide (s ≤ bitsToNat index)
  have h := UnrankInv.step q.isLt hiv hleft
  change UnrankInv W (bitsToNat index) (q.val+1) (2*bitsToNat code+right.toNat)
    (if right then s else bitsToNat lower) at h
  have hcode : 2*bitsToNat code+right.toNat < 2^n :=
    h.1.trans_le (Nat.pow_le_pow_right (by decide) q.isLt)
  rw [bitsToNat_natToBits hcode]
  by_cases hr : right = true
  · rw [ite_eq_left hr, bitsToNat_natToBits hsum]
    simpa only [ite_eq_left hr] using h
  · rw [ite_eq_right hr]
    simpa only [ite_eq_right hr] using h

end PEqualNP.Outside.L_pcx_436_aux
namespace PEqualNP.Outside.L_pcx_436_aux

open scoped BigOperators

abbrev decoderArity (n m b d : ℕ) : ℕ :=
  2+(m*(b+b)+(n*2+((m+1)+((m+1)+((m+1)+d)))))

def blockIdx {l w : ℕ} (e : Fin l) (j : Fin w) : Fin (l*w) :=
  ⟨e.val*w+j.val, by
    have hl := Nat.mul_le_mul_right w (Nat.succ_le_of_lt e.isLt)
    change (e.val+1)*w ≤ l*w at hl
    rw [Nat.add_mul, Nat.one_mul] at hl
    exact (Nat.add_lt_add_left j.isLt _).trans_le hl⟩

theorem encodeBlocks_get {l w : ℕ} (hw : 0 < w) (f : Fin l → Fin w → Bool)
    (e : Fin l) (j : Fin w) : encodeBlocks hw f (blockIdx e j) = f e j := by
  have hq : (e.val*w+j.val)/w = e.val := by
    have hr : e.val*w+j.val < (e.val+1)*w := by rw [Nat.add_mul, Nat.one_mul]; omega
    exact Nat.div_eq_of_lt_le (by omega) hr
  have hm : (e.val*w+j.val)%w = j.val := by
    rw [Nat.add_mod, Nat.mul_mod_left, zero_add, Nat.mod_mod, Nat.mod_eq_of_lt j.isLt]
  unfold encodeBlocks blockIdx
  rw [show (⟨(e.val*w+j.val)/w, _⟩ : Fin l) = e from Fin.ext hq,
    show (⟨(e.val*w+j.val)%w, _⟩ : Fin w) = j from Fin.ext hm]

def weightsVector {m b : ℕ} (w : Fin m → Bool → Fin (2^b)) : Fin (m*(b+b)) → Bool :=
  fun i => if h : 0 < b+b then encodeBlocks h (edgeWord w) i
    else False.elim (by
      have hz : b=0 := by omega
      have hi : i.val < 0 := by simpa only [hz, Nat.add_zero, Nat.mul_zero] using i.isLt
      exact Nat.not_lt_zero _ hi)

theorem weightsVector_ofFn {m b : ℕ} (w : Fin m → Bool → Fin (2^b)) :
    List.ofFn (weightsVector w) = weightsList b w := by
  by_cases h : 0 < b+b
  · have hword : weightsVector w = encodeBlocks h (edgeWord w) := by
      funext i
      rw [weightsVector, dite_eq_left h]
    rw [hword, encodeBlocks_ofFn]
    simp only [edgeWord_ofFn, weightsList, inputBits]
  · have hz : b=0 := by omega
    subst b
    simp [weightsList, inputBits, List.ofFn_zero, List.ofFn_const]

def boolIndex (k : Bool) : Fin 2 := ⟨k.toNat, by cases k <;> decide⟩

def weightIndex {m b : ℕ} (e : Fin m) (k : Bool) (j : Fin b) : Fin (m*(b+b)) :=
  blockIdx e (if k then j.natAdd b else j.castAdd b)

theorem weightsVector_get {m b : ℕ} (w : Fin m → Bool → Fin (2^b)) (e : Fin m) (k : Bool) (j : Fin b) :
    weightsVector w (weightIndex e k j) = natToBits b (w e k).val j := by
  have hb : 0 < b+b := by have := j.isLt; omega
  simp only [weightsVector, dite_eq_left hb, weightIndex, encodeBlocks_get, edgeWord]
  cases k <;> simp only [Bool.false_eq_true, ite_false, ite_true, Fin.append_left, Fin.append_right]

def permissionBlock {n : ℕ} (p : Fin n → Bool → Bool) : Fin (n*2) → Bool :=
  encodeBlocks (by decide) (fun i j => p i (decide (j.val = 1)))

theorem permissionBlock_ofFn {n : ℕ} (p : Fin n → Bool → Bool) :
    List.ofFn (permissionBlock p) = (List.ofFn fun i => [p i false,p i true]).flatten := by
  rw [permissionBlock, encodeBlocks_ofFn]
  rfl

theorem permissionBlock_get {n : ℕ} (p : Fin n → Bool → Bool) (i : Fin n) (k : Bool) :
    permissionBlock p (blockIdx i (boolIndex k)) = p i k := by
  rw [permissionBlock, encodeBlocks_get]
  cases k <;> rfl

def hotVector {q : ℕ} (i : Fin q) (j : Fin q) : Bool := decide (j = i)

def readWeights {n m b d : ℕ} (x : Fin (decoderArity n m b d) → Bool) (e : Fin m) (k : Bool) (j : Fin b) :
    Bool := x ((weightIndex e k j).castAdd (n*2+((m+1)+((m+1)+((m+1)+d)))) |>.natAdd 2)

def readPermission {n m b d : ℕ} (x : Fin (decoderArity n m b d) → Bool) (i : Fin n) (k : Bool) :
    Bool := x ((((blockIdx i (boolIndex k)).castAdd ((m+1)+((m+1)+((m+1)+d)))).natAdd (m*(b+b))).natAdd 2)

def readHot {n m b d : ℕ} (x : Fin (decoderArity n m b d) → Bool)
    (j : Fin ((m+1)+((m+1)+((m+1)+d)))) : Bool :=
  x (((j.natAdd (n*2)).natAdd (m*(b+b))).natAdd 2)

def hot1 {n m b d : ℕ} (x : Fin (decoderArity n m b d) → Bool) (j : Fin (m+1)) : Bool :=
  readHot x (j.castAdd ((m+1)+((m+1)+d)))

def hot2 {n m b d : ℕ} (x : Fin (decoderArity n m b d) → Bool) (j : Fin (m+1)) : Bool :=
  readHot x ((j.castAdd ((m+1)+d)).natAdd (m+1))

def hot3 {n m b d : ℕ} (x : Fin (decoderArity n m b d) → Bool) (j : Fin (m+1)) : Bool :=
  readHot x (((j.castAdd d).natAdd (m+1)).natAdd (m+1))

def readOffset {n m b d : ℕ} (x : Fin (decoderArity n m b d) → Bool) (j : Fin d) : Bool :=
  readHot x (((j.natAdd (m+1)).natAdd (m+1)).natAdd (m+1))

def inputVector {n m b d : ℕ} (w : Fin m → Bool → Fin (2^b)) (p : Fin n → Bool → Bool)
    (a t h : Fin (m+1)) (offset : Fin (2^d)) : Fin (decoderArity n m b d) → Bool :=
  Fin.append (![false,true] : Fin 2 → Bool)
    (Fin.append (weightsVector w) (Fin.append (permissionBlock p)
      (Fin.append (hotVector a) (Fin.append (hotVector t) (Fin.append (hotVector h) (natToBits d offset.val))))))

theorem inputVector_ofFn {n m b d : ℕ} (w : Fin m → Bool → Fin (2^b)) (p : Fin n → Bool → Bool)
    (a t h : Fin (m+1)) (offset : Fin (2^d)) :
    List.ofFn (inputVector w p a t h offset) =
      [false,true] ++ weightsList b w ++ (List.ofFn fun i => [p i false,p i true]).flatten ++
      List.ofFn (hotVector a) ++ List.ofFn (hotVector t) ++ List.ofFn (hotVector h) ++ inputBits d offset.val := by
  simp only [inputVector, List.ofFn_fin_append, weightsVector_ofFn, permissionBlock_ofFn, List.append_assoc]
  rfl

def decodeWeights {n m b d : ℕ} (x : Fin (decoderArity n m b d) → Bool)
    (e : Fin m) (k : Bool) : Fin (2^b) :=
  ⟨bitsToNat (readWeights x e k), bitsToNat_lt _⟩

theorem readWeights_circuit {n m b d : ℕ} (e : Fin m) (k : Bool) :
    HasCirc (decoderArity n m b d) b 0
      (fun x => natToBits b (decodeWeights x e k).val) := by
  simp only [decodeWeights, natToBits_bitsToNat]
  exact HasCirc.proj _

theorem readPermission_circuit {n m b d : ℕ} (i : Fin n) (k : Bool) :
    HasCirc (decoderArity n m b d) 1 0 (fun x _ => readPermission x i k) :=
  HasCirc.proj _

theorem inputVector_weights {n m b d : ℕ} (w : Fin m → Bool → Fin (2^b)) (p : Fin n → Bool → Bool)
    (a t h : Fin (m+1)) (offset : Fin (2^d)) :
    decodeWeights (inputVector w p a t h offset) = w := by
  funext e k
  apply Fin.ext
  have hread : readWeights (inputVector w p a t h offset) e k = natToBits b (w e k).val := by
    funext j
    simp only [readWeights, inputVector, Fin.append_left, Fin.append_right, weightsVector_get]
  change bitsToNat (readWeights (inputVector w p a t h offset) e k) = _
  rw [hread, bitsToNat_natToBits (w e k).isLt]

theorem inputVector_permission {n m b d : ℕ} (w : Fin m → Bool → Fin (2^b)) (p : Fin n → Bool → Bool)
    (a t h : Fin (m+1)) (offset : Fin (2^d)) :
    readPermission (inputVector w p a t h offset) = p := by
  funext i k
  simp only [readPermission, inputVector, Fin.append_left, Fin.append_right, permissionBlock_get]

theorem inputVector_hot {n m b d : ℕ} (w : Fin m → Bool → Fin (2^b)) (p : Fin n → Bool → Bool)
    (a t h : Fin (m+1)) (offset : Fin (2^d)) :
    let x := inputVector w p a t h offset
    hot1 x = hotVector a ∧ hot2 x = hotVector t ∧ hot3 x = hotVector h ∧ readOffset x = natToBits d offset.val := by
  dsimp only
  refine ⟨?_,?_,?_,?_⟩ <;> funext j
  · simp only [hot1, readHot, inputVector, Fin.append_left, Fin.append_right]
  · simp only [hot2, readHot, inputVector, Fin.append_left, Fin.append_right]
  · simp only [hot3, readHot, inputVector, Fin.append_left, Fin.append_right]
  · simp only [readOffset, readHot, inputVector, Fin.append_right]

end PEqualNP.Outside.L_pcx_436_aux
namespace PEqualNP.Outside.L_pcx_436_aux

open scoped BigOperators
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

def cellTriple {P : ℕ} (k : Fin ((P*P)*P)) : Fin P × Fin P × Fin P :=
  let i : Fin (P*P) × Fin P := finProdFinEquiv.symm k
  let j : Fin P × Fin P := finProdFinEquiv.symm i.1
  (i.2,j.2,j.1)

theorem triple_cellTriple {P : ℕ} (k : Fin ((P*P)*P)) :
    tripleCode (cellTriple k).1 (cellTriple k).2.1 (cellTriple k).2.2 = k := by
  let i : Fin (P*P) × Fin P := finProdFinEquiv.symm k
  let j : Fin P × Fin P := finProdFinEquiv.symm i.1
  change finProdFinEquiv (finProdFinEquiv (j.1,j.2),i.2) = k
  rw [Prod.mk.eta, show finProdFinEquiv j = i.1 from Equiv.apply_symm_apply _ _,
    Prod.mk.eta, show finProdFinEquiv i = k from Equiv.apply_symm_apply _ _]

def pickRaw {n m b d : ℕ} (x : Fin (decoderArity n m b d) → Bool)
    (k : Fin (((m+1)*(m+1))*(m+1))) : Bool :=
  let (a,t,h) := cellTriple k
  (hot1 x a && hot2 x t) && hot3 x h

theorem pickRaw_circ {n m b d : ℕ} (k : Fin (((m+1)*(m+1))*(m+1))) :
    HasCirc (decoderArity n m b d) 1 2 (fun x _ => pickRaw x k) :=
  HasCirc.and2 (HasCirc.and2 (HasCirc.proj _) (HasCirc.proj _)) (HasCirc.proj _)

theorem pickRaw_input {n m b d : ℕ} (w : Fin m → Bool → Fin (2^b)) (p : Fin n → Bool → Bool)
    (a t h : Fin (m+1)) (offset : Fin (2^d)) (k : Fin (((m+1)*(m+1))*(m+1))) :
    pickRaw (inputVector w p a t h offset) k = decide (k=tripleCode a t h) := by
  have hy := inputVector_hot w p a t h offset
  dsimp only at hy
  change ((hot1 _ (cellTriple k).1 && hot2 _ (cellTriple k).2.1) &&
    hot3 _ (cellTriple k).2.2) = _
  rw [hy.1,hy.2.1,hy.2.2.1]
  rw [Bool.eq_iff_iff]
  simp only [hotVector, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨ha,ht⟩,hh⟩
    simpa only [ha,ht,hh] using (triple_cellTriple k).symm
  · intro hk
    obtain ⟨ha,ht,hh⟩ := tripleCode_eq.mp ((triple_cellTriple k).trans hk)
    exact ⟨⟨ha,ht⟩,hh⟩

def prefixBudget (n m f c b D s : ℕ) : ℕ :=
  let B := (n+m+f+b+2)^4
  let L := (n+m*b+1)*(((m+1)*(m+1))*(m+1))
  let W := L+(n+f)+D
  2*W + ((m+n+1)*2^(f+c))*(termBudget n m f B W s 2+(16*W+2))

def constructionBudget (n m f c b D s : ℕ) : ℕ :=
  let d := n+m*b+1
  let K := ((m+1)*(m+1))*(m+1)
  let P := prefixBudget n m f c b D s
  let A := P+d*(2+K*4)
  let Flag := A+(17*d+6)
  P+Flag+((2*(n+d)+n*(3*A+100*(d+1)))+Flag+2+4*n)

theorem keyMass_triple {n m f : ℕ} (u v : Fin m → Fin n) (color : Fin m → Fin 3) (face : Fin n → Option (Fin f))
    (w : Fin m → Bool → ℕ) (p : Fin n → Bool → Bool) (a t h : Fin (m+1)) (x : Fin (2^n)) :
    keyMass u v color face w p (tripleCode a t h) x =
      if (∀ i, (face i).isSome = true → p i (msbSpin x i) = true) ∧
        (Finset.univ.filter (fun e : Fin m => color e = 0 ∧ spinDiff u v x e = true)).card = a.val ∧
        (Finset.univ.filter (fun e : Fin m => color e = 1 ∧ spinDiff u v x e = true)).card = t.val ∧
        (Finset.univ.filter (fun e : Fin m => color e = 2 ∧ spinDiff u v x e = true)).card = h.val
      then ∏ e : Fin m, w e (spinDiff u v x e) else 0 := by
  unfold keyMass histogramLabel
  simp only [tripleCode_eq]
  simp only [Fin.ext_iff, tallyFin]

set_option maxHeartbeats 2000000 in
theorem completeConstruction {n m f c b D s : ℕ} (hn : 0 < n)
    (u v : Fin m → Fin n) (color : Fin m → Fin 3) (face : Fin n → Option (Fin f))
    (hconn : ∀ a b, Relation.ReflTransGen (Adj u v) a b) (hface : ∀ g, ∃ a, face a = some g)
    (hreps : ∀ q ≤ n, ∃ R : Finset (Fin n), R.card ≤ c ∧ ∀ a, a.val < q →
      ∃ r ∈ R, r.val < q ∧ Relation.ReflTransGen (fun i j => i.val < q ∧ j.val < q ∧ Adj u v i j) a r)
    {B : ℕ} {g : Circuit} {out : Fin D → Fin (2+2*(m+n)*B+g.size)}
    (hG : ReadsBack (2+2*(m+n)*B) g) (hlegal : ∀ g' ∈ g.gates, ValidGate g') (hsize : g.size ≤ s)
    (heval : ∀ w' : Fin (m+n) → Bool → Fin (2^B),
      bitsToNat (fun j => (g.wires ([false,true] ++ weightsList B w')).getD (out j).val false) =
        zeroField u v face w')
    (hB : B = (n+m+f+b+2)^4) :
    let d := n+m*b+1
    let K := ((m+1)*(m+1))*(m+1)
    let N := decoderArity n m b d
    ∃ (g' : Circuit) (hist : Fin K → Fin d → Fin (N+g'.size))
      (ok : Fin (N+g'.size)) (word : Fin n → Fin (N+g'.size)),
      ReadsBack N g' ∧ (∀ g'' ∈ g'.gates, ValidGate g'') ∧ g'.size ≤ constructionBudget n m f c b D s ∧
      ∀ (w : Fin m → Bool → Fin (2^b)) (p : Fin n → Bool → Bool) (a t h : Fin (m+1)) (offset : Fin (2^d)),
        let z := g'.wires (List.ofFn (inputVector w p a t h offset))
        let M := keyMass u v color face (fun e k => (w e k).val) p
        (∀ k : Fin K, bitsToNat (fun j : Fin d => z.getD (hist k j).val false) = ∑ x, M k x) ∧
        z.getD ok.val false = decide (offset.val < ∑ x, M (tripleCode a t h) x) ∧
        let picked := ∑ i : Fin n, (z.getD (word i).val false).toNat*2^(n-1-i.val)
        if offset.val < ∑ x, M (tripleCode a t h) x then
          ∃ x : Fin (2^n), x.val = picked ∧
            (∑ y ∈ Finset.univ.filter (fun y : Fin (2^n) => y < x), M (tripleCode a t h) y) ≤ offset.val ∧
            offset.val < (∑ y ∈ Finset.univ.filter (fun y : Fin (2^n) => y ≤ x), M (tripleCode a t h) y)
        else picked = 0 := by
  classical
  subst B
  dsimp only
  let d := n+m*b+1
  let K := ((m+1)*(m+1))*(m+1)
  let N := decoderArity n m b d
  let P := prefixBudget n m f c b D s
  let A := P+d*(2+K*4)
  have hd : 0 < d := by dsimp [d]; omega
  have hN : 0 < N := by dsimp [N,decoderArity]; omega
  let root : Fin n := ⟨0,hn⟩
  let W (x : Fin N → Bool) := decodeWeights x
  let Perm (x : Fin N → Bool) := readPermission x
  let selected (x : Fin N → Bool) := pickRaw x
  let offsetBits (x : Fin N → Bool) := readOffset x
  have hOff : HasCirc N d 0 offsetBits := HasCirc.proj _
  have hW (e : Fin m) (k : Bool) : HasCirc N b 0 (fun x => natToBits b (W x e k).val) :=
    readWeights_circuit e k
  have hPerm (i : Fin n) (k : Bool) : HasCirc N 1 0 (fun x _ => Perm x i k) := readPermission_circuit i k
  have hSelected (k : Fin K) : HasCirc N 1 2 (fun x _ => selected x k) := pickRaw_circ k
  let emptyHist (x : Fin N → Bool) := natToBits (d*K)
    (packedPrefix d u v color face (fun _ => false) (fun _ => false) (fun e k => (W x e k).val) (Perm x))
  have hEmpty : HasCirc N (d*K) P emptyHist := by
    obtain ⟨R,hR,hpath⟩ := hreps 0 (by omega)
    have hEmptyPath : ∀ a : Fin n, (false : Bool) = true → ∃ r ∈ R, (false : Bool) = true ∧
        Relation.ReflTransGen (fun i j => (false : Bool) = true ∧ (false : Bool) = true ∧ Adj u v i j) a r := by
      intro i hi
      cases hi
    exact HasCirc.buildPackedPrefix (T := 2) hN hn u v color face root (hconn root) hface
      (fun _ => false) R hR hEmptyPath (fun _ _ => false) W Perm (fun _ => HasCirc.const hN false)
      (fun e k => (hW e k).weaken (by decide)) (fun i k => (hPerm i k).weaken (by decide)) hG hlegal hsize heval
  let initScore (x : Fin N → Bool) := readCell (selected x) (emptyHist x)
  have hInit : HasCirc N d A initScore := HasCirc.addressed hN hSelected hEmpty
  let flag (x : Fin N → Bool) := decide (bitsToNat (offsetBits x) < bitsToNat (initScore x))
  have hFlag : HasCirc N 1 (A+(17*d+6)) (fun x _ => flag x) := by
    refine (HasCirc.not1 (HasCirc.geWords hd hOff hInit)).weaken (by omega) |>.congr ?_
    intro x j
    change (!(decide (bitsToNat (initScore x) ≤ bitsToNat (offsetBits x)))) =
      decide (bitsToNat (offsetBits x) < bitsToNat (initScore x))
    by_cases ht : bitsToNat (initScore x) ≤ bitsToNat (offsetBits x)
    · rw [decide_eq_true ht, decide_eq_false (not_lt_of_ge ht)]
      rfl
    · rw [decide_eq_false ht, decide_eq_true (lt_of_not_ge ht)]
      rfl
  let prefixInputs (x : Fin (N+(n+d)) → Bool) := fun j : Fin N => x (j.castAdd (n+d))
  let code (x : Fin (N+(n+d)) → Bool) := fun j : Fin n => x ((j.castAdd d).natAdd N)
  let lower (x : Fin (N+(n+d)) → Bool) := fun j : Fin d => x ((j.natAdd n).natAdd N)
  have hcode : HasCirc (N+(n+d)) n 0 code := HasCirc.proj _
  have hlower : HasCirc (N+(n+d)) d 0 lower := HasCirc.proj _
  have hX : 0 < N+(n+d) := by omega
  let leftHist (q : Fin n) (x : Fin (N+(n+d)) → Bool) := natToBits (d*K)
    (packedPrefix d u v color face (fun i => decide (i.val < q.val+1)) (leftTarget q (code x))
      (fun e k => (W (prefixInputs x) e k).val) (Perm (prefixInputs x)))
  have hLeft (q : Fin n) : HasCirc (N+(n+d)) (d*K) P (leftHist q) := by
    obtain ⟨R,hR,hpath⟩ := hreps (q.val+1) q.isLt
    exact HasCirc.buildPackedPrefix (T := 2) hX hn u v color face root (hconn root) hface
      (fun i => decide (i.val < q.val+1)) R hR (by simp only [decide_eq_true_eq]; exact hpath)
      (fun x => leftTarget q (code x)) (fun x => W (prefixInputs x)) (fun x => Perm (prefixInputs x))
      (fun i => HasCirc.leftSpin hX q hcode i)
      (fun e k => ((hW e k).reindex _).weaken (by decide))
      (fun i k => ((hPerm i k).reindex _).weaken (by decide)) hG hlegal hsize heval
  let score (q : Fin n) (x : Fin (N+(n+d)) → Bool) := readCell (selected (prefixInputs x)) (leftHist q x)
  have hScore (q : Fin n) : HasCirc (N+(n+d)) d A (score q) :=
    HasCirc.addressed hX (fun i => (hSelected i).reindex _) (hLeft q)
  let step (q : Fin n) (x : Fin (N+(n+d)) → Bool) :=
    unrankRound (code x) (lower x) (score q x) (offsetBits (prefixInputs x))
  have hStep (q : Fin n) : HasCirc (N+(n+d)) (n+d) (3*A+100*(d+1)) (step q) :=
    HasCirc.unrankRound hX hn hd hcode hlower (hScore q) (hOff.reindex _)
  let state (x : Fin N → Bool) := (List.finRange n).foldl
    (fun st i => step i (Fin.append x st)) (natToBits (n+d) 0)
  have hState : HasCirc N (n+d) (2*(n+d)+n*(3*A+100*(d+1))) state :=
    HasCirc.foldl (HasCirc.constBits hN 0) n step hStep
  let wordVal (x : Fin N → Bool) (i : Fin n) :=
    if flag x then state x (i.rev.castAdd d) else false
  have hWord' : HasCirc N n ((2*(n+d)+n*(3*A+100*(d+1)))+(A+(17*d+6))+2+4*n) wordVal := by

    have hz : HasCirc N n 2 (fun _ _ => false) :=
      (HasCirc.const hN false).outputs (fun _ : Fin n => (0 : Fin 1))
    refine (HasCirc.muxWords hFlag (hState.outputs (fun i : Fin n => i.rev.castAdd d)) hz).weaken (by omega)
  have hall := HasCirc.pair hEmpty (HasCirc.pair hFlag hWord')
  obtain ⟨C,outC,hBack,hGate,hCost,hEval⟩ := hall
  refine ⟨C, (fun k j => outC ((cellBit k j).castAdd (1+n))),
    outC ((Fin.castAdd n (0 : Fin 1)).natAdd (d*K)),
    (fun i => outC ((i.natAdd 1).natAdd (d*K))), hBack, hGate, ?_, ?_⟩
  · change C.size ≤ P+(A+(17*d+6))+((2*(n+d)+n*(3*A+100*(d+1)))+(A+(17*d+6))+2+4*n)
    omega
  intro w p a t h idx
  dsimp only

  let x := inputVector w p a t h idx
  let key := tripleCode a t h
  let M := keyMass u v color face (fun e k => (w e k).val) p
  have hWx : W x = w := inputVector_weights w p a t h idx
  have hPx : Perm x = p := inputVector_permission w p a t h idx
  have hSel (i : Fin K) : selected x i = decide (i=key) := pickRaw_input w p a t h idx i
  have hIdx : bitsToNat (offsetBits x) = idx.val := by
    rw [show offsetBits x = natToBits d idx.val from (inputVector_hot w p a t h idx).2.2.2,
      bitsToNat_natToBits idx.isLt]
  have hTotal (k : Fin K) : (∑ y, M k y) < 2^d := keyMass_lt u v color face w p k
  have hHist (k : Fin K) (j : Fin d) : emptyHist x (cellBit k j) = natToBits d (∑ y, M k y) j := by
    unfold emptyHist natToBits
    rw [hWx,hPx]
    exact readInitial u v color face w p (fun _ => false) k j
  have hInitScore : bitsToNat (initScore x) = ∑ y, M key y := by
    have he : initScore x = natToBits d (∑ y, M key y) := funext fun j =>
      (readCell_single key hSel j).trans (hHist key j)
    rw [he, bitsToNat_natToBits (hTotal key)]
  have hValid : flag x = decide (idx.val < ∑ y, M key y) := by
    unfold flag
    rw [hIdx,hInitScore]
  have hEval1 (k : Fin K) (j : Fin d) :
      (C.wires (List.ofFn x)).getD (outC ((cellBit k j).castAdd (1+n))).val false = emptyHist x (cellBit k j) := by
    simpa only [Fin.append_left] using hEval x ((cellBit k j).castAdd (1+n))
  have hEval2 : (C.wires (List.ofFn x)).getD
      (outC ((Fin.castAdd n (0 : Fin 1)).natAdd (d*K))).val false = flag x := by
    simpa only [Fin.append_left,Fin.append_right] using hEval x ((Fin.castAdd n (0 : Fin 1)).natAdd (d*K))
  have hEval3 (i : Fin n) : (C.wires (List.ofFn x)).getD
      (outC ((i.natAdd 1).natAdd (d*K))).val false = wordVal x i := by
    simpa only [Fin.append_right] using hEval x ((i.natAdd 1).natAdd (d*K))
  refine ⟨fun k => ?_, hEval2.trans hValid, ?_⟩
  · change bitsToNat (fun j => (C.wires (List.ofFn x)).getD
      (outC ((cellBit k j).castAdd (1+n))).val false) = ∑ y, M k y
    simp_rw [hEval1,hHist]
    exact bitsToNat_natToBits (hTotal k)
  · let picked := ∑ i : Fin n, ((C.wires (List.ofFn x)).getD
        (outC ((i.natAdd 1).natAdd (d*K))).val false).toNat*2^(n-1-i.val)
    change if idx.val < ∑ y, M key y then
      ∃ z : Fin (2^n), z.val = picked ∧
        (∑ y ∈ Finset.univ.filter (fun y : Fin (2^n) => y < z), M key y) ≤ idx.val ∧
        idx.val < (∑ y ∈ Finset.univ.filter (fun y : Fin (2^n) => y ≤ z), M key y)
      else picked = 0
    have hpicked : picked = ∑ i : Fin n, (wordVal x i).toNat*2^(n-1-i.val) := by
      unfold picked
      exact Finset.sum_congr rfl (fun i _ => by rw [hEval3 i])
    rw [hpicked]
    split_ifs with hv
    · have hInvariant : UnrankInv (M key) idx.val n
          (bitsToNat (fun i : Fin n => state x (i.castAdd d)))
          (bitsToNat (fun i : Fin d => state x (i.natAdd n))) := by
        unfold state
        apply invariant_fold (fun q st => step q (Fin.append x st)) (natToBits (n+d) 0)
          (fun q st => UnrankInv (M key) idx.val q
            (bitsToNat (fun i : Fin n => st (i.castAdd d)))
            (bitsToNat (fun i : Fin d => st (i.natAdd n))))
        · have hz (j : ℕ) : Nat.testBit 0 j = false := by simp
          have h0 : bitsToNat (natToBits n 0) = 0 := bitsToNat_natToBits (by positivity)
          have h1 : bitsToNat (natToBits d 0) = 0 := bitsToNat_natToBits (by positivity)
          have hzero (p q : ℕ) (g : Fin p → Fin q) :
              (fun j => natToBits q 0 (g j)) = natToBits p 0 := by funext j; simp only [natToBits,hz]
          rw [hzero n (n+d), hzero d (n+d), h0,h1]
          exact UnrankInv.init hv
        · intro q st hq
          let y := Fin.append x st
          have hy : prefixInputs y = x := by funext j; simp only [prefixInputs,y,Fin.append_left]
          have hc' : code y = fun i : Fin n => st (i.castAdd d) := by
            funext i
            change (Fin.append x st) ((i.castAdd d).natAdd N) = _
            exact Fin.append_right _ _ _
          have hl' : lower y = fun i : Fin d => st (i.natAdd n) := by
            funext i
            change (Fin.append x st) ((i.natAdd n).natAdd N) = _
            exact Fin.append_right _ _ _
          have hc : bitsToNat (code y) < 2^q.val := by rw [hc']; exact hq.1
          let left := intervalWeight (M key) (bitsToNat (code y)*2^(n-q.val))
            ((2*bitsToNat (code y)+1)*2^(n-(q.val+1)))
          have hleft_lt : left < 2^d := by
            unfold left intervalWeight
            exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset ..)
              (fun _ _ _ => Nat.zero_le _)).trans_lt (hTotal key)
          have hscore : score q y = natToBits d left := by
            funext j
            unfold score
            rw [hy, readCell_single key hSel]
            unfold leftHist natToBits
            rw [hy,hWx,hPx]
            exact readLeft u v color face w p key q (code y) hc j
          have hi : bitsToNat (offsetBits (prefixInputs y)) = idx.val := by rw [hy,hIdx]
          have hInv : UnrankInv (M key) (bitsToNat (offsetBits (prefixInputs y))) q.val
              (bitsToNat (code y)) (bitsToNat (lower y)) := by
            rw [hi,hc',hl']
            exact hq
          have hu := unrankRound_inv q (code y) (lower y) (score q y)
            (offsetBits (prefixInputs y)) hInv (by rw [hscore,bitsToNat_natToBits hleft_lt]) (hTotal key)
          rw [hi] at hu
          exact hu
      have hpick : (∑ i : Fin n, (wordVal x i).toNat*2^(n-1-i.val)) =
          bitsToNat (fun i : Fin n => state x (i.castAdd d)) := by
        have ht : flag x = true := hValid.trans (decide_eq_true hv)
        have he := (spinEquiv_weight (fun i : Fin n => state x (i.rev.castAdd d))).symm
        change _ = bitsToNat (fun i : Fin n => state x (i.rev.rev.castAdd d)) at he
        simpa only [wordVal,ht,ite_true,Fin.rev_rev] using he
      rw [hpick]
      exact UnrankInv.finish hInvariant
    · have hf : flag x = false := hValid.trans (decide_eq_false hv)
      simp [wordVal,hf]

end PEqualNP.Outside.L_pcx_436_aux
namespace PEqualNP.Outside.L_pcx_436_aux

set_option maxHeartbeats 2000000 in
theorem constructionBudget_bound (n m f c b s : ℕ) (hn : 0 < n) :
    let H := n+m+f+b+2
    let D := n+f+(m+n)*H^4+1
    constructionBudget n m f c b D s ≤ (s+1)*H^20*2^(f+c) := by
  dsimp only
  generalize hHdef : n+m+f+b+2 = H
  let D := n+f+(m+n)*H^4+1
  change constructionBudget n m f c b D s ≤ _
  let M := m+n
  let d := n+m*b+1
  let K := ((m+1)*(m+1))*(m+1)
  let L := d*K
  let W := L+(n+f)+D
  let F := 2^(f+c)
  let S := s+1
  have hH : 3 ≤ H := by omega
  have hM : M+2 ≤ H := by dsimp only [M]; omega
  have hm : m+1 ≤ H := by omega
  have hn' : n ≤ H := by omega
  have hnf : n+f+1 ≤ H := by omega
  have hb : b ≤ H := by omega
  have hpow (a b : ℕ) (hne : a ≤ b) : H^a ≤ H^b := Nat.pow_le_pow_right (by omega) hne
  have hd : d ≤ H^2 := by
    have hm' : m ≤ H := by omega
    have h1 : m*b ≤ m*H := Nat.mul_le_mul_left _ hb
    have h2 : n+1 ≤ (H-m)*H := by
      calc
        _ ≤ H-m := by omega
        _ = (H-m)*1 := by simp
        _ ≤ _ := Nat.mul_le_mul_left _ (by omega)
    calc
      d ≤ m*H+(H-m)*H := by dsimp [d]; omega
      _ = H^2 := by rw [← Nat.add_mul, Nat.add_sub_cancel' hm', pow_two]
  have hK : K ≤ H^3 := by
    calc
      K ≤ (H*H)*H := Nat.mul_le_mul (Nat.mul_le_mul hm hm) hm
      _ = H^3 := by ring
  have hL : L ≤ H^5 := by
    calc
      L ≤ H^2*H^3 := Nat.mul_le_mul hd hK
      _ = _ := by ring
  have hD : D ≤ H+H^5 := by
    have hmul : M*H^4 ≤ H^5 := by
      calc
        _ ≤ H*H^4 := Nat.mul_le_mul_right _ (by omega)
        _ = _ := by ring
    dsimp only [D]
    change (m+n)*H^4 ≤ H^5 at hmul
    omega
  have hW : W ≤ 4*H^5 := by
    have h := hpow 1 5 (by decide)
    simp only [pow_one] at h
    dsimp only [W]
    omega
  let X := inputWeightBudget M (H^4) 2
  have hX : X ≤ 100*H^5 := by
    calc
      X ≤ 6+H*(18*H^4+4)+8*H^4+14 := by
        dsimp only [X,inputWeightBudget]
        exact Nat.add_le_add_right (Nat.add_le_add_right
          (Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _) _) _
      _ ≤ _ := by
        have h45 := hpow 4 5 (by decide)
        have h15 := hpow 1 5 (by decide)
        have h05 := hpow 0 5 (by decide)
        nlinarith only [h45,h15,h05]
  let Q := 4+M*(X+X)+s+2
  have hQ : Q ≤ 206*H^6+s := by
    calc
      Q ≤ 4+H*(100*H^5+100*H^5)+s+2 := by
        dsimp only [Q]
        exact Nat.add_le_add_right (Nat.add_le_add_right
          (Nat.add_le_add_left (Nat.mul_le_mul (by omega) (Nat.add_le_add hX hX)) _) _) _
      _ ≤ _ := by have h06 := hpow 0 6 (by decide); nlinarith only [h06]
  let P0 := 8+(n+f)*(2+6)
  have hP0 : P0 ≤ 16*H^6 := by
    have h16 := hpow 1 6 (by decide)
    have h06 := hpow 0 6 (by decide)
    simp only [pow_one,pow_zero] at h16 h06
    dsimp only [P0]
    omega
  let A0 := Q+(2*W+(M+2)*(18*W+4))
  have hA0 : A0 ≤ 290*H^6+s := by
    calc
      A0 ≤ (206*H^6+s)+(2*(4*H^5)+H*(18*(4*H^5)+4)) := by
        dsimp only [A0]
        exact Nat.add_le_add hQ (Nat.add_le_add (Nat.mul_le_mul_left _ hW)
          (Nat.mul_le_mul hM (Nat.add_le_add_right (Nat.mul_le_mul_left _ hW) _)))
      _ ≤ _ := by
        have h56 := hpow 5 6 (by decide)
        have h16 := hpow 1 6 (by decide)
        nlinarith only [h56,h16]
  have hTerm : termBudget n m f (H^4) W s 2+(16*W+2) ≤ 2000*H^6*S := by
    change P0+(2*W+A0+(17*W+5)+A0)+4*W+(16*W+2) ≤ _
    have h56 := hpow 5 6 (by decide)
    have h06 : 1 ≤ H^6 := by simpa using hpow 0 6 (by decide)
    have hs : s ≤ H^6*s := by simpa using Nat.mul_le_mul_right s h06
    dsimp only [S]
    nlinarith only [hP0,hW,hA0,h56,h06,hs]
  have hF : 1 ≤ F := by dsimp [F]; exact Nat.one_le_two_pow
  have hS : 1 ≤ S := by dsimp [S]; omega
  let U := H^7*S*F
  have hU (p : ℕ) (hp : p ≤ 7) : H^p ≤ U :=
    (hpow _ _ hp).trans ((by
      simpa using Nat.mul_le_mul_left (H^7) hS : H^7 ≤ H^7*S).trans (by
      simpa using Nat.mul_le_mul_left (H^7*S) hF))
  let P := prefixBudget n m f c b D s
  have hP : P ≤ 3000*U := by
    unfold P prefixBudget
    dsimp only
    rw [hHdef]
    change 2*W+((M+1)*F)*(termBudget n m f (H^4) W s 2+(16*W+2)) ≤ _
    calc
      _ ≤ 2*(4*H^5)+(H*F)*(2000*H^6*S) := Nat.add_le_add
        (Nat.mul_le_mul_left _ hW) (Nat.mul_le_mul (Nat.mul_le_mul_right _ (by omega)) hTerm)
      _ = 8*H^5+2000*U := by dsimp [U]; ring
      _ ≤ _ := by have h := hU 5 (by decide); omega
  let A := P+d*(2+K*4)
  have hA : A ≤ 4000*U := by
    calc
      A ≤ 3000*U+H^2*(2+H^3*4) := Nat.add_le_add hP
        (Nat.mul_le_mul hd (Nat.add_le_add_left (Nat.mul_le_mul_right _ hK) _))
      _ = 3000*U+2*H^2+4*H^5 := by ring
      _ ≤ _ := by have h2 := hU 2 (by decide); have h5 := hU 5 (by decide); omega
  let Flag := A+(17*d+6)
  have hFlag : Flag ≤ 5000*U := by
    have h2 := hU 2 (by decide)
    have h0 : 1 ≤ U := by simpa using hU 0 (by decide)
    dsimp only [Flag]
    omega
  let T := H*U
  have hUT : U ≤ T := by simpa [T] using Nat.mul_le_mul_right U (show 1 ≤ H by omega)
  have hstep : 3*A+100*(d+1) ≤ 13000*U := by
    have h2 := hU 2 (by decide)
    have h0 : 1 ≤ U := by simpa using hU 0 (by decide)
    omega
  have hNstep : n*(3*A+100*(d+1)) ≤ 13000*T := by
    calc
      _ ≤ H*(13000*U) := Nat.mul_le_mul hn' hstep
      _ = _ := by dsimp only [T]; ring
  have hOverall : constructionBudget n m f c b D s ≤ 30000*T := by
    change P+Flag+((2*(n+d)+n*(3*A+100*(d+1)))+Flag+2+4*n) ≤ _
    have h1 : H ≤ U := by simpa using hU 1 (by decide)
    have h2 := hU 2 (by decide)
    have h0 : 1 ≤ U := by simpa using hU 0 (by decide)
    omega
  refine hOverall.trans ?_
  have hC : 30000 ≤ H^12 := by
    exact (by decide : 30000 ≤ 3^12).trans (Nat.pow_le_pow_left hH _)
  calc
    30000*T ≤ H^12*T := Nat.mul_le_mul_right _ hC
    _ = (s+1)*H^20*2^(f+c) := by dsimp only [T,U,S,F]; ring

end PEqualNP.Outside.L_pcx_436_aux
open PEqualNP.Outside.L_pcx_436_aux

set_option maxHeartbeats 600000 in
theorem PEqualNP.Outside.L_pcx_436 : (∃ C : ℕ, 0 < C ∧ ∀ (n m f c b s : ℕ) (u v : Fin m → Fin n)
  (color : Fin m → Fin 3) (face : Fin n → Option (Fin f)),
  0 < n →
  let I := Fin n
  let E := Fin m
  let adj := fun x y : I => ∃ e, (u e = x ∧ v e = y) ∨ (u e = y ∧ v e = x)
  (∀ i j : I, Relation.ReflTransGen adj i j) →
  (∀ j : Fin f, ∃ i, face i = some j) →
  (∀ q ≤ n, ∃ R : Finset I, R.card ≤ c ∧ ∀ i : I, i.val < q →
    ∃ j ∈ R, j.val < q ∧ Relation.ReflTransGen
      (fun x y : I => x.val < q ∧ y.val < q ∧ adj x y) i j) →
  let legal := fun (N : ℕ) (g : PEqualNP.CircuitLowerBounds.Circuit) =>
    PEqualNP.MetaComplexity.NestedCover.ReadsBack N g ∧ ∀ a ∈ g.gates,
      ((a.op = .and ∨ a.op = .or) ∧ a.inputs.length = 2) ∨
      (a.op = .not ∧ a.inputs.length = 1)
  let H := n+m+f+b+2
  let B := H^4
  let bits := fun (d x : ℕ) => List.ofFn (fun j : Fin d => x.testBit j.val)
  let weights := fun (l d : ℕ) (w : Fin l → Bool → Fin (2^d)) =>
    (List.ofFn (fun e : Fin l => bits d (w e false).val ++ bits d (w e true).val)).flatten
  let D := n+f+(m+n)*B+1
  let N := 2+2*(m+n)*B
  (∃ (g : PEqualNP.CircuitLowerBounds.Circuit) (out : Fin D → Fin (N+g.size)),
    legal N g ∧ g.size ≤ s ∧ ∀ w : Fin (m+n) → Bool → Fin (2^B),
      let ws := g.wires ([false,true] ++ weights (m+n) B w)
      (∑ j : Fin D, (ws.getD (out j).val false).toNat*2^j.val) =
        ∑ x : I → Bool, ∑ y : Fin f → Bool,
          (∏ e : E, (w (Fin.castAdd n e) (xor (x (u e)) (x (v e)))).val) *
          ∏ i : I, (face i).elim 1 (fun j => (w (Fin.natAdd m i) (xor (x i) (y j))).val)) →
  let J := Fin (m+1)
  let d := n+m*b+1
  let N' := 2+2*m*b+2*n+3*(m+1)+d
  ∃ (g : PEqualNP.CircuitLowerBounds.Circuit) (out : J → J → J → Fin d → Fin (N'+g.size))
    (flag : Fin (N'+g.size)) (word : I → Fin (N'+g.size)),
    legal N' g ∧ g.size ≤ (s+1)*H^C*2^(f+c) ∧
    ∀ (w : E → Bool → Fin (2^b)) (p : I → Bool → Bool) (a t h : J) (index : Fin (2^d)),
      let hot := fun (j : J) => List.ofFn (fun l : J => decide (l = j))
      let ws := g.wires ([false,true] ++ weights m b w ++
        (List.ofFn (fun i : I => [p i false,p i true])).flatten ++
        hot a ++ hot t ++ hot h ++ bits d index.val)
      let spin := fun (x : Fin (2^n)) (i : I) => x.val.testBit (n-1-i.val)
      let mass := fun (l r z : J) (x : Fin (2^n)) =>
        let diff := fun e : E => xor (spin x (u e)) (spin x (v e))
        let tally := fun j : Fin 3 => (Finset.univ.filter (fun e : E => color e = j ∧ diff e = true)).card
        if (∀ i : I, (face i).isSome = true → p i (spin x i) = true) ∧
          tally 0 = l.val ∧ tally 1 = r.val ∧ tally 2 = z.val then
          ∏ e : E, (w e (diff e)).val else 0
      let total := fun l r z => ∑ x, mass l r z x
      (∀ l r z, (∑ j : Fin d, (ws.getD (out l r z j).val false).toNat*2^j.val) = total l r z) ∧
      ws.getD flag.val false = decide (index.val < total a t h) ∧
      let picked := ∑ i : I, (ws.getD (word i).val false).toNat*2^(n-1-i.val)
      if index.val < total a t h then ∃ x : Fin (2^n), x.val = picked ∧
        (∑ y ∈ Finset.univ.filter (fun y : Fin (2^n) => y < x), mass a t h y) ≤ index.val ∧
        index.val < (∑ y ∈ Finset.univ.filter (fun y : Fin (2^n) => y ≤ x), mass a t h y)
      else picked = 0
) := by
  classical
  refine ⟨20, by decide, ?_⟩
  intro n m f c b s u v color face hn
  dsimp only
  intro hconn hface hreps horacle
  let H := n+m+f+b+2
  let B := H^4
  let D := n+f+(m+n)*B+1
  let d := n+m*b+1
  obtain ⟨g,out,⟨hg,hlegal⟩,hsize,hev⟩ := horacle
  have heval (w' : Fin (m+n) → Bool → Fin (2^B)) :
      bitsToNat (fun j : Fin D => (g.wires ([false,true] ++ weightsList B w')).getD (out j).val false) =
        zeroField u v face w' := hev w'
  obtain ⟨g',hist,ok,word,hBack,hGate,hC,hProof⟩ :=
    completeConstruction (c := c) (D := D) (B := B) (s := s) (g := g) (out := out)
      hn u v color face hconn hface hreps hg hlegal hsize heval rfl
  have hN : decoderArity n m b d = 2+2*m*b+2*n+3*(m+1)+d := by unfold decoderArity; ring
  rw [← hN]
  refine ⟨g', (fun l r z => hist (tripleCode l r z)), ok, word, ⟨hBack,hGate⟩,
    hC.trans (constructionBudget_bound n m f c b s hn), ?_⟩
  intro w p a t h index
  have hout := hProof w p a t h index
  dsimp only at hout
  rw [inputVector_ofFn] at hout
  have hhot (q : Fin (m+1)) : List.ofFn (hotVector q) =
      List.ofFn (fun j : Fin (m+1) => decide (j=q)) := rfl
  simp_rw [hhot] at hout
  rcases hout with ⟨hHist,hOther⟩
  refine ⟨fun l r z => ?_, ?_⟩
  · have hr := hHist (tripleCode l r z)
    simp only [bitsToNat, weightsList, inputBits, keyMass_triple, msbSpin, spinDiff, List.append_assoc] at hr
    simp only [List.append_assoc]
    convert hr using 1
    all_goals rfl
  · simp only [weightsList, inputBits, keyMass_triple, msbSpin, spinDiff, List.append_assoc] at hOther
    simp only [List.append_assoc]
    convert hOther using 1
    all_goals rfl
