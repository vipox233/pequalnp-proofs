import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_38505

def nl (g : Gate) : Bool :=
  (g.inputs.length == 2) &&
    xor (xor (g.op.eval [false,false]) (g.op.eval [false,true]))
        (xor (g.op.eval [true,false]) (g.op.eval [true,true]))

def inp (n r c : ℕ) (x : Fin n → Fin r) (y : Fin n → Fin c) : List Bool :=
  (List.ofFn (fun j : Fin n => PEqualNP.Represents.oneEach (x j) (y j))).flatten

def wr (gs : List Gate) (l : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) l

def dps (W : ℕ) (gs : List Gate) : List ℕ :=
  gs.foldl (fun (ds : List Nat) g =>
      ds ++ [(g.inputs.map (fun i => ds.getD i 0)).foldr max 0 + (nl g).toNat])
      (List.replicate W 0)

theorem wr_snoc (gs : List Gate) (g : Gate) (l : List Bool) :
    wr (gs ++ [g]) l
      = wr gs l ++ [g.op.eval (g.inputs.map fun i => (wr gs l).getD i false)] := by
  simp [wr, List.foldl_append]

theorem wr_length (gs : List Gate) (l : List Bool) :
    (wr gs l).length = l.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [wr]
  | append_singleton gs g ih =>
    rw [wr_snoc]
    simp only [List.length_append, List.length_singleton, ih]
    omega

theorem dps_snoc (W : ℕ) (gs : List Gate) (g : Gate) :
    dps W (gs ++ [g])
      = dps W gs ++ [(g.inputs.map (fun i => (dps W gs).getD i 0)).foldr max 0 + (nl g).toNat] := by
  simp [dps, List.foldl_append]

theorem dps_length (W : ℕ) (gs : List Gate) : (dps W gs).length = W + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [dps]
  | append_singleton gs g ih =>
    rw [dps_snoc]
    simp only [List.length_append, List.length_singleton, ih]
    omega

theorem wr_app_getD (gs ex : List Gate) (l : List Bool) (i : ℕ) (h : i < l.length + gs.length) :
    (wr (gs ++ ex) l).getD i false = (wr gs l).getD i false := by
  induction ex using List.reverseRecOn with
  | nil => simp
  | append_singleton ex g ih =>
    have hlt : i < (wr (gs ++ ex) l).length := by
      rw [wr_length, List.length_append]; omega
    rw [← List.append_assoc, wr_snoc, List.getD_append _ _ _ _ hlt, ih]

theorem dps_app_getD (W : ℕ) (gs ex : List Gate) (i : ℕ) (h : i < W + gs.length) :
    (dps W (gs ++ ex)).getD i 0 = (dps W gs).getD i 0 := by
  induction ex using List.reverseRecOn with
  | nil => simp
  | append_singleton ex g ih =>
    have hlt : i < (dps W (gs ++ ex)).length := by
      rw [dps_length, List.length_append]; omega
    rw [← List.append_assoc, dps_snoc, List.getD_append _ _ _ _ hlt, ih]

theorem wr_snoc_new (gs : List Gate) (g : Gate) (l : List Bool) :
    (wr (gs ++ [g]) l).getD (l.length + gs.length) false
      = g.op.eval (g.inputs.map fun i => (wr gs l).getD i false) := by
  have hle : (wr gs l).length ≤ l.length + gs.length := by rw [wr_length]
  rw [wr_snoc, List.getD_append_right _ _ _ _ hle, wr_length]
  simp

theorem dps_snoc_new (W : ℕ) (gs : List Gate) (g : Gate) :
    (dps W (gs ++ [g])).getD (W + gs.length) 0
      = (g.inputs.map (fun i => (dps W gs).getD i 0)).foldr max 0 + (nl g).toNat := by
  have hle : (dps W gs).length ≤ W + gs.length := by rw [dps_length]
  rw [dps_snoc, List.getD_append_right _ _ _ _ hle, dps_length]
  simp

theorem flat_length (L : ℕ) (ls : List (List Bool)) :
    (∀ s ∈ ls, s.length = L) → ls.flatten.length = ls.length * L := by
  induction ls with
  | nil => intro _; simp
  | cons s t ih =>
    intro h
    have hs : s.length = L := h s (by simp)
    have ht := ih (fun u hu => h u (by simp [hu]))
    simp only [List.flatten_cons, List.length_append, List.length_cons, hs, ht]
    ring

theorem flat_getD (L : ℕ) (a : ℕ) (ha : a < L) (ls : List (List Bool)) :
    (∀ s ∈ ls, s.length = L) → ∀ j : ℕ,
      ls.flatten.getD (j * L + a) false = (ls.getD j []).getD a false := by
  induction ls with
  | nil => intro _ j; simp
  | cons s t ih =>
    intro h j
    have hs : s.length = L := h s (by simp)
    have ht := ih (fun u hu => h u (by simp [hu]))
    cases j with
    | zero =>
      simp only [List.flatten_cons, Nat.zero_mul, Nat.zero_add, List.getD_cons_zero]
      exact List.getD_append _ _ _ _ (by omega)
    | succ j =>
      have hle : s.length ≤ (j + 1) * L + a := by rw [hs, Nat.succ_mul]; omega
      have hsub : (j + 1) * L + a - s.length = j * L + a := by rw [hs, Nat.succ_mul]; omega
      simp only [List.flatten_cons, List.getD_cons_succ]
      rw [List.getD_append_right _ _ _ _ hle, hsub]
      exact ht j

theorem one_len (n r c : ℕ) (x : Fin n → Fin r) (y : Fin n → Fin c) :
    ∀ s ∈ List.ofFn (fun j : Fin n => PEqualNP.Represents.oneEach (x j) (y j)),
      s.length = r + c := by
  intro s hs
  obtain ⟨j, rfl⟩ : ∃ j : Fin n, PEqualNP.Represents.oneEach (x j) (y j) = s := by
    simpa [List.mem_ofFn] using hs
  simp [PEqualNP.Represents.oneEach]

theorem inp_length (n r c : ℕ) (x : Fin n → Fin r) (y : Fin n → Fin c) :
    (inp n r c x y).length = n * (r + c) := by
  unfold inp
  rw [flat_length (r + c) _ (one_len n r c x y)]
  simp

theorem inp_getD (n r c : ℕ) (x : Fin n → Fin r) (y : Fin n → Fin c) (j : ℕ) (hj : j < n)
    (a : ℕ) (ha : a < r + c) :
    (inp n r c x y).getD (j * (r + c) + a) false
      = (PEqualNP.Represents.oneEach (x ⟨j, hj⟩) (y ⟨j, hj⟩)).getD a false := by
  unfold inp
  rw [flat_getD (r + c) a ha _ (one_len n r c x y) j]
  have hlt : j < (List.ofFn (fun j : Fin n => PEqualNP.Represents.oneEach (x j) (y j))).length := by
    simpa using hj
  rw [List.getD_eq_getElem _ _ hlt]
  simp

theorem ofFn_getD_lt {α : Type} (m : ℕ) (f : Fin m → α) (d : α) (a : ℕ) (ha : a < m) :
    (List.ofFn f).getD a d = f ⟨a, ha⟩ := by
  have hlt : a < (List.ofFn f).length := by simpa using ha
  rw [List.getD_eq_getElem _ _ hlt]
  simp

theorem one_getD_lt (r c : ℕ) (u : Fin r) (v : Fin c) (a : ℕ) (ha : a < r) :
    (PEqualNP.Represents.oneEach u v).getD a false = decide (a = u.val) := by
  unfold PEqualNP.Represents.oneEach
  have hlt : a < (List.ofFn (fun i : Fin r => decide (i = u))).length := by simpa using ha
  rw [List.getD_append _ _ _ _ hlt, ofFn_getD_lt r _ false a ha]
  simp [Fin.ext_iff]

theorem one_getD_ge (r c : ℕ) (u : Fin r) (v : Fin c) (a : ℕ) (ha : r ≤ a) :
    (PEqualNP.Represents.oneEach u v).getD a false
      = (List.ofFn (fun j : Fin c => decide (j = v))).getD (a - r) false := by
  unfold PEqualNP.Represents.oneEach
  have hle : (List.ofFn (fun i : Fin r => decide (i = u))).length ≤ a := by simpa using ha
  rw [List.getD_append_right _ _ _ _ hle]
  simp

theorem one_getD_col (r c : ℕ) (u : Fin r) (v : Fin c) (b : ℕ) (hb : b < c) :
    (PEqualNP.Represents.oneEach u v).getD (r + b) false = decide (b = v.val) := by
  rw [one_getD_ge r c u v (r + b) (Nat.le_add_right r b), Nat.add_sub_cancel_left,
    ofFn_getD_lt c _ false b hb]
  simp [Fin.ext_iff]

def tF (b : Bool) : ZMod 2 := if b then 1 else 0

def ind (s t : Fin 3) : ZMod 2 := if s = t then 1 else 0

def dl (n r c : ℕ) (L : (Fin n → Fin r) → (Fin n → Fin c) → ZMod 2) :
    (Fin n → Fin r) → (Fin n → Fin r) → (Fin n → Fin c) → (Fin n → Fin c) → ZMod 2 :=
  fun x x' y y' => L x y + L x' y + L x y' + L x' y'

def wf (n r c : ℕ) (gs : List Gate) (i : ℕ) : (Fin n → Fin r) → (Fin n → Fin c) → ZMod 2 :=
  fun x y => tF ((wr gs (inp n r c x y)).getD i false)

theorem z4 : ∀ a : ZMod 2, a + a + a + a = 0 := by decide
theorem zabab : ∀ a b : ZMod 2, a + b + a + b = 0 := by decide
theorem zaabb : ∀ a b : ZMod 2, a + a + b + b = 0 := by decide
theorem two0 : (2 : ZMod 2) = 0 := by decide

theorem dl_aff (n r c : ℕ) (h f g : (Fin n → Fin r) → (Fin n → Fin c) → ZMod 2)
    (k0 k1 k2 : ZMod 2) (H : ∀ x y, h x y = k0 + k1 * f x y + k2 * g x y) :
    dl n r c h = k1 • dl n r c f + k2 • dl n r c g := by
  funext x x' y y'
  simp only [dl, Pi.add_apply, Pi.smul_apply, smul_eq_mul, H]
  linear_combination (2 * k0) * two0

theorem inp_dl0 (n r c : ℕ) (i : ℕ) : dl n r c (wf n r c [] i) = 0 := by
  funext x x' y y'
  simp only [dl, wf, wr, List.foldl_nil, Pi.zero_apply]
  by_cases hi : i < n * (r + c)
  · have hL : 0 < r + c := by
      rcases Nat.eq_zero_or_pos (r + c) with h0 | h0
      · rw [h0] at hi; simp at hi
      · exact h0
    have hj : i / (r + c) < n := by
      rw [Nat.div_lt_iff_lt_mul hL]; exact hi
    have ha : i % (r + c) < r + c := Nat.mod_lt _ hL
    have hi' : i / (r + c) * (r + c) + i % (r + c) = i := Nat.div_add_mod' i (r + c)
    have key : ∀ (u : Fin n → Fin r) (v : Fin n → Fin c), (inp n r c u v).getD i false
        = (PEqualNP.Represents.oneEach (u ⟨i / (r + c), hj⟩) (v ⟨i / (r + c), hj⟩)).getD
            (i % (r + c)) false := by
      intro u v
      have h := inp_getD n r c u v (i / (r + c)) hj (i % (r + c)) ha
      rw [hi'] at h
      exact h
    by_cases har : i % (r + c) < r
    · simp only [key, one_getD_lt r c _ _ _ har]
      exact zabab _ _
    · have har' : r ≤ i % (r + c) := by omega
      simp only [key, one_getD_ge r c _ _ _ har']
      exact zaabb _ _
  · have hlen : ∀ (u : Fin n → Fin r) (v : Fin n → Fin c),
        (inp n r c u v).getD i false = false := fun u v =>
      List.getD_eq_default _ _ (by rw [inp_length]; omega)
    simp only [hlen]
    decide

theorem aff1 : ∀ p q b : Bool, tF (bif b then q else p) = tF p + (tF p + tF q) * tF b := by
  decide

theorem aff2 : ∀ f00 f01 f10 f11 a b : Bool, xor (xor f00 f01) (xor f10 f11) = false →
    tF (bif a then (bif b then f11 else f10) else (bif b then f01 else f00))
      = tF f00 + (tF f00 + tF f10) * tF a + (tF f00 + tF f01) * tF b := by
  decide

theorem gate_aff (g : Gate) (h2 : g.inputs.length ≤ 2) (hn : nl g = false) :
    ∃ (k0 k1 k2 : ZMod 2) (a b : ℕ), ∀ v : ℕ → Bool,
      tF (g.op.eval (g.inputs.map v)) = k0 + k1 * tF (v a) + k2 * tF (v b) := by
  obtain ⟨op, ins⟩ := g
  match ins, h2, hn with
  | [], _, _ => exact ⟨tF (op.eval []), 0, 0, 0, 0, fun v => by simp⟩
  | [a], _, _ =>
    refine ⟨tF (op.eval [false]), tF (op.eval [false]) + tF (op.eval [true]), 0, a, 0,
      fun v => ?_⟩
    have e : op.eval [v a] = (bif v a then op.eval [true] else op.eval [false]) := by
      cases v a <;> rfl
    simp only [List.map_cons, List.map_nil, e, aff1, zero_mul, add_zero]
  | [a, b], _, hn =>
    have hx : xor (xor (op.eval [false,false]) (op.eval [false,true]))
        (xor (op.eval [true,false]) (op.eval [true,true])) = false := hn
    refine ⟨tF (op.eval [false,false]), tF (op.eval [false,false]) + tF (op.eval [true,false]),
      tF (op.eval [false,false]) + tF (op.eval [false,true]), a, b, fun v => ?_⟩
    have e : op.eval [v a, v b]
        = (bif v a then (bif v b then op.eval [true,true] else op.eval [true,false])
            else (bif v b then op.eval [false,true] else op.eval [false,false])) := by
      cases v a <;> cases v b <;> rfl
    simp only [List.map_cons, List.map_nil, e]
    exact aff2 _ _ _ _ _ _ hx
  | _ :: _ :: _ :: _, h2, _ =>
    exfalso
    simp only [List.length_cons] at h2
    omega

theorem span_wires (n r c : ℕ) : ∀ gs : List Gate, (∀ g ∈ gs, g.inputs.length ≤ 2) →
    ∃ T : Finset ((Fin n → Fin r) → (Fin n → Fin r) → (Fin n → Fin c) → (Fin n → Fin c) → ZMod 2),
      T.card ≤ gs.countP nl ∧
      ∀ i, dl n r c (wf n r c gs i) ∈ Submodule.span (ZMod 2) (T : Set _) := by
  classical
  intro gs
  induction gs using List.reverseRecOn with
  | nil =>
    intro _
    exact ⟨∅, by simp, fun i => by rw [inp_dl0]; exact Submodule.zero_mem _⟩
  | append_singleton gs g ih =>
    intro h2
    obtain ⟨T, hT, hmem⟩ := ih (fun g' hg' => h2 g' (by simp [hg']))
    have hg2 : g.inputs.length ≤ 2 := h2 g (by simp)
    have hold : ∀ i, i ≠ n * (r + c) + gs.length →
        wf n r c (gs ++ [g]) i = wf n r c gs i := by
      intro i hi
      funext x y
      simp only [wf]
      congr 1
      rcases Nat.lt_or_gt_of_ne hi with h | h
      · exact wr_app_getD gs [g] _ i (by rw [inp_length]; exact h)
      · have e1 : (wr (gs ++ [g]) (inp n r c x y)).getD i false = false :=
          List.getD_eq_default _ _ (by
            rw [wr_length, inp_length, List.length_append, List.length_singleton]; omega)
        have e2 : (wr gs (inp n r c x y)).getD i false = false :=
          List.getD_eq_default _ _ (by rw [wr_length, inp_length]; omega)
        rw [e1, e2]
    have hnew : ∀ x y, (wr (gs ++ [g]) (inp n r c x y)).getD (n * (r + c) + gs.length) false
        = g.op.eval (g.inputs.map fun i => (wr gs (inp n r c x y)).getD i false) := by
      intro x y
      have h := wr_snoc_new gs g (inp n r c x y)
      rw [inp_length] at h
      exact h
    by_cases hnl : nl g = true
    · refine ⟨insert (dl n r c (wf n r c (gs ++ [g]) (n * (r + c) + gs.length))) T, ?_, ?_⟩
      · have h1 := Finset.card_insert_le
          (dl n r c (wf n r c (gs ++ [g]) (n * (r + c) + gs.length))) T
        have h3 : (gs ++ [g]).countP nl = gs.countP nl + 1 := by
          simp [List.countP_append, hnl]
        omega
      · intro i
        by_cases hi : i = n * (r + c) + gs.length
        · rw [hi]; exact Submodule.subset_span (by simp)
        · rw [hold i hi]
          exact Submodule.span_mono (by simp) (hmem i)
    · have hnl' : nl g = false := by simpa using hnl
      refine ⟨T, ?_, ?_⟩
      · have h3 : gs.countP nl ≤ (gs ++ [g]).countP nl := by simp [List.countP_append]
        omega
      · intro i
        by_cases hi : i = n * (r + c) + gs.length
        · obtain ⟨k0, k1, k2, a, b, hk⟩ := gate_aff g hg2 hnl'
          have hd := dl_aff n r c (wf n r c (gs ++ [g]) (n * (r + c) + gs.length))
            (wf n r c gs a) (wf n r c gs b) k0 k1 k2 (fun x y => by
              simp only [wf]
              rw [hnew x y]
              exact hk (fun i => (wr gs (inp n r c x y)).getD i false))
          rw [hi, hd]
          exact Submodule.add_mem _ (Submodule.smul_mem _ _ (hmem a))
            (Submodule.smul_mem _ _ (hmem b))
        · rw [hold i hi]; exact hmem i

theorem sel0 : ∀ p0 p1 p2 q0 q1 q2 : Bool, p0 ≠ p1 → q0 ≠ q2 →
    ∃ k α β : ZMod 2, k + α * tF p0 + β * tF q0 = 1 ∧ k + α * tF p1 + β * tF q1 = 0 ∧
      k + α * tF p2 + β * tF q2 = 0 := by
  decide

theorem fin3_cover : ∀ t t' t'' s : Fin 3, t ≠ t' → t ≠ t'' → t' ≠ t'' →
    s = t ∨ s = t' ∨ s = t'' := by
  decide

theorem fin3_third (i p q s : Fin 3) (h1 : i ≠ p) (h2 : i ≠ q) (h3 : p ≠ q) (h4 : s ≠ p)
    (h5 : s ≠ i) : s = q := by
  rcases fin3_cover i p q s h1 h2 h3 with h | h | h
  · exact absurd h h5
  · exact absurd h h4
  · exact h

theorem card_le_of_li {K V ι : Type} [CommRing K] [Nontrivial K] [AddCommGroup V] [Module K V]
    [Fintype ι] (v : ι → V) (hv : LinearIndependent K v) (T : Finset V)
    (hin : ∀ i, v i ∈ Submodule.span K (T : Set V)) : Fintype.card ι ≤ T.card := by
  have : Module.Finite K (Submodule.span K (T : Set V)) := Module.Finite.span_finset K T
  have hli' := hv.codRestrict (Submodule.span K (T : Set V)) hin
  have h1 := hli'.fintype_card_le_finrank
  have h4 : Module.finrank K (Submodule.span K (T : Set V)) ≤ T.card :=
    finrank_span_finset_le_card (R := K) T
  exact le_trans h1 h4

theorem E_aff (w : ℕ) (key : Fin 3 → Fin w → Bool) (hinj : Function.Injective key)
    (t t' t'' : Fin 3) (h1 : t ≠ t') (h2 : t ≠ t'') (h3 : t' ≠ t'') :
    ∃ (k α β : ZMod 2) (b1 b2 : Fin w), ∀ s : Fin 3,
      ind s t = k + α * tF (key s b1) + β * tF (key s b2) := by
  obtain ⟨b1, hb1⟩ := Function.ne_iff.mp (hinj.ne h1)
  obtain ⟨b2, hb2⟩ := Function.ne_iff.mp (hinj.ne h2)
  obtain ⟨k, α, β, e1, e2, e3⟩ := sel0 (key t b1) (key t' b1) (key t'' b1)
    (key t b2) (key t' b2) (key t'' b2) hb1 hb2
  refine ⟨k, α, β, b1, b2, fun s => ?_⟩
  rcases fin3_cover t t' t'' s h1 h2 h3 with hs | hs | hs
  · rw [hs, e1]; simp [ind]
  · rw [hs, e2]; simp [ind, Ne.symm h1]
  · rw [hs, e3]; simp [ind, Ne.symm h2]

theorem sum_single (n : ℕ) (F : Fin n → ZMod 2) (j0 : Fin n) (hz : ∀ j, j ≠ j0 → F j = 0) :
    ∑ j, F j = F j0 :=
  Finset.sum_eq_single j0 (fun j _ hj => hz j hj) (fun h => absurd (Finset.mem_univ _) h)

theorem cellsum (n r c : ℕ) (rowOK : Fin r → Fin 3 → Prop) (colOK : Fin c → Fin 3 → Prop)
    (sel : (Fin n → Fin r) → (Fin n → Fin c) → Fin n → Fin 3)
    (hrow : ∀ x y j, rowOK (x j) (sel x y j)) (hcol : ∀ x y j, colOK (y j) (sel x y j))
    (R : Fin 3 → Fin r) (C : Fin 3 → Fin c)
    (hR : ∀ i, ¬ rowOK (R i) i) (hC : ∀ i, ¬ colOK (C i) i)
    (cf : Fin n × Bool → ZMod 2)
    (hsum : ∀ x x' y y', ∑ j : Fin n,
      (cf (j, true) * dl n r c (fun x y => ind (sel x y j) 1) x x' y y'
        + cf (j, false) * dl n r c (fun x y => ind (sel x y j) 0) x x' y y') = 0)
    (j0 : Fin n) (i p q : Fin 3) (hip : i ≠ p) (hiq : i ≠ q) (hpq : p ≠ q) :
    ∃ s : Fin 3, s ≠ i ∧
      cf (j0, true) * (ind s 1 + ind q 1 + ind p 1 + ind i 1)
        + cf (j0, false) * (ind s 0 + ind q 0 + ind p 0 + ind i 0) = 0 := by
  classical
  obtain ⟨X, hX⟩ : ∃ X : Fin 3 → Fin n → Fin r,
      ∀ a j, X a j = if j = j0 then R a else R 1 := ⟨_, fun _ _ => rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y : Fin 3 → Fin n → Fin c,
      ∀ b j, Y b j = if j = j0 then C b else C 2 := ⟨_, fun _ _ => rfl⟩
  have hoth : ∀ a b j, j ≠ j0 → sel (X a) (Y b) j = 0 := by
    intro a b j hj
    have h1 := hrow (X a) (Y b) j
    have h2 := hcol (X a) (Y b) j
    rw [hX, if_neg hj] at h1
    rw [hY, if_neg hj] at h2
    have e1 : sel (X a) (Y b) j ≠ 1 := fun e => hR 1 (by rw [e] at h1; exact h1)
    have e2 : sel (X a) (Y b) j ≠ 2 := fun e => hC 2 (by rw [e] at h2; exact h2)
    exact fin3_third 1 2 0 _ (by decide) (by decide) (by decide) e2 e1
  have hj0 : ∀ a b, sel (X a) (Y b) j0 ≠ a ∧ sel (X a) (Y b) j0 ≠ b := by
    intro a b
    have h1 := hrow (X a) (Y b) j0
    have h2 := hcol (X a) (Y b) j0
    rw [hX, if_pos rfl] at h1
    rw [hY, if_pos rfl] at h2
    exact ⟨fun e => hR a (by rw [e] at h1; exact h1), fun e => hC b (by rw [e] at h2; exact h2)⟩
  have hz : ∀ j, j ≠ j0 →
      cf (j, true) * dl n r c (fun x y => ind (sel x y j) 1) (X i) (X p) (Y i) (Y q)
        + cf (j, false) * dl n r c (fun x y => ind (sel x y j) 0) (X i) (X p) (Y i) (Y q) = 0 := by
    intro j hj
    simp only [dl, hoth _ _ j hj, z4, mul_zero, add_zero]
  have h := (sum_single n _ j0 hz).symm.trans (hsum (X i) (X p) (Y i) (Y q))
  simp only [dl] at h
  have e1 : sel (X p) (Y i) j0 = q :=
    fin3_third i p q _ hip hiq hpq (hj0 p i).1 (hj0 p i).2
  have e2 : sel (X i) (Y q) j0 = p :=
    fin3_third i q p _ hiq hip (Ne.symm hpq) (hj0 i q).2 (hj0 i q).1
  have e3 : sel (X p) (Y q) j0 = i :=
    fin3_third p q i _ hpq (Ne.symm hip) (Ne.symm hiq) (hj0 p q).2 (hj0 p q).1
  rw [e1, e2, e3] at h
  exact ⟨sel (X i) (Y i) j0, (hj0 i i).1, h⟩

theorem comb : ∀ (s0 s1 s2 : Fin 3) (c0 c1 : ZMod 2), s0 ≠ 0 → s1 ≠ 1 → s2 ≠ 2 →
    c1 * (ind s0 1 + ind 2 1 + ind 1 1 + ind 0 1)
      + c0 * (ind s0 0 + ind 2 0 + ind 1 0 + ind 0 0) = 0 →
    c1 * (ind s1 1 + ind 2 1 + ind 0 1 + ind 1 1)
      + c0 * (ind s1 0 + ind 2 0 + ind 0 0 + ind 1 0) = 0 →
    c1 * (ind s2 1 + ind 1 1 + ind 0 1 + ind 2 1)
      + c0 * (ind s2 0 + ind 1 0 + ind 0 0 + ind 2 0) = 0 →
    c0 = 0 ∧ c1 = 0 := by
  decide

theorem indep (n r c : ℕ) (rowOK : Fin r → Fin 3 → Prop) (colOK : Fin c → Fin 3 → Prop)
    (sel : (Fin n → Fin r) → (Fin n → Fin c) → Fin n → Fin 3)
    (hrow : ∀ x y j, rowOK (x j) (sel x y j)) (hcol : ∀ x y j, colOK (y j) (sel x y j))
    (hRex : ∀ i, ∃ x, ¬ rowOK x i) (hCex : ∀ i, ∃ y, ¬ colOK y i) :
    LinearIndependent (ZMod 2) (fun p : Fin n × Bool =>
      dl n r c (fun x y => ind (sel x y p.1) (bif p.2 then 1 else 0))) := by
  classical
  choose R hR using hRex
  choose C hC using hCex
  rw [Fintype.linearIndependent_iff]
  intro cf hcf
  have hsum : ∀ x x' y y', ∑ j : Fin n,
      (cf (j, true) * dl n r c (fun x y => ind (sel x y j) 1) x x' y y'
        + cf (j, false) * dl n r c (fun x y => ind (sel x y j) 0) x x' y y') = 0 := by
    intro x x' y y'
    have h := congrFun (congrFun (congrFun (congrFun hcf x) x') y) y'
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, Pi.zero_apply, cond_true, cond_false] at h
    exact h
  have main : ∀ j0, cf (j0, false) = 0 ∧ cf (j0, true) = 0 := by
    intro j0
    obtain ⟨s0, hs0, h0⟩ := cellsum n r c rowOK colOK sel hrow hcol R C hR hC cf hsum j0 0 1 2
      (by decide) (by decide) (by decide)
    obtain ⟨s1, hs1, h1⟩ := cellsum n r c rowOK colOK sel hrow hcol R C hR hC cf hsum j0 1 0 2
      (by decide) (by decide) (by decide)
    obtain ⟨s2, hs2, h2⟩ := cellsum n r c rowOK colOK sel hrow hcol R C hR hC cf hsum j0 2 0 1
      (by decide) (by decide) (by decide)
    exact comb s0 s1 s2 _ _ hs0 hs1 hs2 h0 h1 h2
  rintro ⟨j, b⟩
  cases b
  · exact (main j).1
  · exact (main j).2

set_option maxHeartbeats 1000000 in
theorem lower (n r c w : ℕ) (rowOK : Fin r → Fin 3 → Prop) (colOK : Fin c → Fin 3 → Prop)
    (key : Fin 3 → Fin w → Bool) (hinj : Function.Injective key)
    (hmiss : ∀ i, (∃ x, ¬ rowOK x i) ∧ (∃ y, ¬ colOK y i))
    (gs : List Gate) (tap : Fin n → Fin w → ℕ) (h2 : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (hfit : ∀ (x : Fin n → Fin r) (y : Fin n → Fin c) (j : Fin n), ∃ i,
      rowOK (x j) i ∧ colOK (y j) i ∧
      ∀ b, (wr gs (inp n r c x y)).getD (tap j b) false = key i b) :
    2 * n ≤ gs.countP nl := by
  classical
  choose sel hsel using hfit
  obtain ⟨T, hT, hmem⟩ := span_wires n r c gs h2
  have hli := indep n r c rowOK colOK sel (fun x y j => (hsel x y j).1)
    (fun x y j => (hsel x y j).2.1) (fun i => (hmiss i).1) (fun i => (hmiss i).2)
  have hin : ∀ p : Fin n × Bool,
      dl n r c (fun x y => ind (sel x y p.1) (bif p.2 then 1 else 0))
        ∈ Submodule.span (ZMod 2) (T : Set _) := by
    rintro ⟨j, b⟩
    have hE : ∀ t t' t'' : Fin 3, t ≠ t' → t ≠ t'' → t' ≠ t'' →
        dl n r c (fun x y => ind (sel x y j) t) ∈ Submodule.span (ZMod 2) (T : Set _) := by
      intro t t' t'' h1 h2' h3
      obtain ⟨k, α, β, b1, b2, hk⟩ := E_aff w key hinj t t' t'' h1 h2' h3
      have hd := dl_aff n r c (fun x y => ind (sel x y j) t) (wf n r c gs (tap j b1))
        (wf n r c gs (tap j b2)) k α β (fun x y => by
          simp only [wf]
          rw [(hsel x y j).2.2 b1, (hsel x y j).2.2 b2]
          exact hk _)
      rw [hd]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ (hmem _))
        (Submodule.smul_mem _ _ (hmem _))
    cases b
    · exact hE 0 1 2 (by decide) (by decide) (by decide)
    · exact hE 1 0 2 (by decide) (by decide) (by decide)
  have h1 := card_le_of_li _ hli T hin
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool] at h1
  omega

def val (n r c : ℕ) (gs : List Gate) (x : Fin n → Fin r) (y : Fin n → Fin c) (i : ℕ) : Bool :=
  (wr gs (inp n r c x y)).getD i false

def dep (n r c : ℕ) (gs : List Gate) (i : ℕ) : ℕ := (dps (n * (r + c)) gs).getD i 0

def Good (n r c : ℕ) (gs : List Gate) : Prop :=
  (∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < n * (r + c) + j) ∧
    ∀ g ∈ gs, g.inputs.length ≤ 2

def Ext (n r c : ℕ) (gs gs' : List Gate) (m : ℕ) : Prop :=
  Good n r c gs' ∧ ∃ ex, gs' = gs ++ ex ∧ ex.countP nl = m

def Has (n r c : ℕ) (gs : List Gate) (k : ℕ)
    (f : (Fin n → Fin r) → (Fin n → Fin c) → Bool) (D : ℕ) : Prop :=
  k < n * (r + c) + gs.length ∧ dep n r c gs k ≤ D ∧ ∀ x y, val n r c gs x y k = f x y

def e0f (a0 b0 : Bool) : Bool := a0 && b0

def e1f (a0 a1 b0 b1 : Bool) : Bool :=
  xor ((xor (!a0) (!b0)) && (xor (a0 && a1) b1)) (!b0)

def selB (a0 a1 b0 b1 : Bool) : Fin 3 :=
  bif e0f a0 b0 then 0 else bif e1f a0 a1 b0 b1 then 1 else 2

theorem ext_refl {n r c : ℕ} {gs : List Gate} (hg : Good n r c gs) : Ext n r c gs gs 0 :=
  ⟨hg, [], (List.append_nil gs).symm, rfl⟩

theorem ext_trans {n r c : ℕ} {a b d : List Gate} {m m' M : ℕ} (h1 : Ext n r c a b m)
    (h2 : Ext n r c b d m') (hM : m + m' = M) : Ext n r c a d M := by
  obtain ⟨_, e1, rfl, c1⟩ := h1
  obtain ⟨hg, e2, rfl, c2⟩ := h2
  exact ⟨hg, e1 ++ e2, List.append_assoc a e1 e2, by rw [List.countP_append, c1, c2, hM]⟩

theorem has_mono {n r c : ℕ} {gs gs' : List Gate} {m k : ℕ}
    {f : (Fin n → Fin r) → (Fin n → Fin c) → Bool} {D : ℕ}
    (hE : Ext n r c gs gs' m) (h : Has n r c gs k f D) : Has n r c gs' k f D := by
  obtain ⟨_, ex, rfl, _⟩ := hE
  obtain ⟨hk, hd, hv⟩ := h
  refine ⟨by rw [List.length_append]; omega, ?_, fun x y => ?_⟩
  · have e : dep n r c (gs ++ ex) k = dep n r c gs k := dps_app_getD _ gs ex k hk
    rw [e]; exact hd
  · have e : val n r c (gs ++ ex) x y k = val n r c gs x y k :=
      wr_app_getD gs ex _ k (by rw [inp_length]; exact hk)
    rw [e]; exact hv x y

theorem has_congr {n r c : ℕ} {gs : List Gate} {k : ℕ}
    {f f' : (Fin n → Fin r) → (Fin n → Fin c) → Bool} {D : ℕ}
    (h : Has n r c gs k f D) (hf : ∀ x y, f x y = f' x y) : Has n r c gs k f' D :=
  ⟨h.1, h.2.1, fun x y => (h.2.2 x y).trans (hf x y)⟩

theorem has_weaken {n r c : ℕ} {gs : List Gate} {k : ℕ}
    {f : (Fin n → Fin r) → (Fin n → Fin c) → Bool} {D D' : ℕ}
    (h : Has n r c gs k f D) (hD : D ≤ D') : Has n r c gs k f D' :=
  ⟨h.1, le_trans h.2.1 hD, h.2.2⟩

theorem op_gate (n r c : ℕ) (gs : List Gate) (g : Gate) (hg : Good n r c gs)
    (hin : ∀ i ∈ g.inputs, i < n * (r + c) + gs.length) (h2 : g.inputs.length ≤ 2) :
    Ext n r c gs (gs ++ [g]) (nl g).toNat ∧
    n * (r + c) + gs.length < n * (r + c) + (gs ++ [g]).length ∧
    dep n r c (gs ++ [g]) (n * (r + c) + gs.length)
      = (g.inputs.map (fun i => dep n r c gs i)).foldr max 0 + (nl g).toNat ∧
    ∀ x y, val n r c (gs ++ [g]) x y (n * (r + c) + gs.length)
      = g.op.eval (g.inputs.map (fun i => val n r c gs x y i)) := by
  refine ⟨⟨⟨?_, ?_⟩, [g], rfl, ?_⟩, ?_, ?_, ?_⟩
  · intro j hj i hi
    rw [List.length_append, List.length_singleton] at hj
    by_cases hjl : j < gs.length
    · rw [List.getD_append _ _ _ _ hjl] at hi
      exact hg.1 j hjl i hi
    · have hje : j = gs.length := by omega
      subst hje
      rw [List.getD_append_right _ _ _ _ (le_refl _)] at hi
      simp at hi
      exact hin i hi
  · intro g' hg'
    rw [List.mem_append] at hg'
    rcases hg' with h | h
    · exact hg.2 g' h
    · rw [List.mem_singleton] at h
      rw [h]; exact h2
  · cases hn : nl g <;> simp [hn]
  · rw [List.length_append, List.length_singleton]; omega
  · exact dps_snoc_new _ gs g
  · intro x y
    have h := wr_snoc_new gs g (inp n r c x y)
    rw [inp_length] at h
    exact h

theorem ev_xnor_not : ∀ p q : Bool, GateOp.not.eval [(GateOp.mod 2).eval [p, q]] = xor p q := by
  decide

theorem ev_and : ∀ p q : Bool, GateOp.and.eval [p, q] = (p && q) := by decide

theorem nl_un (op : GateOp) (a : ℕ) : nl ⟨op, [a]⟩ = false := rfl

theorem nl_mod2 (a b : ℕ) : nl ⟨GateOp.mod 2, [a, b]⟩ = false := rfl

theorem nl_and (a b : ℕ) : nl ⟨GateOp.and, [a, b]⟩ = true := rfl

theorem op_un (n r c : ℕ) (gs : List Gate) (hg : Good n r c gs) (op : GateOp) (a : ℕ)
    (f : (Fin n → Fin r) → (Fin n → Fin c) → Bool) (D : ℕ) (ha : Has n r c gs a f D) :
    Ext n r c gs (gs ++ [⟨op, [a]⟩]) 0 ∧
    Has n r c (gs ++ [⟨op, [a]⟩]) (n * (r + c) + gs.length) (fun x y => op.eval [f x y]) D := by
  obtain ⟨hE, hk, hd, hv⟩ := op_gate n r c gs ⟨op, [a]⟩ hg
    (by intro i hi; simp at hi; rw [hi]; exact ha.1) (by simp)
  rw [nl_un] at hE hd
  refine ⟨hE, hk, ?_, fun x y => ?_⟩
  · rw [hd]
    simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, Bool.toNat_false]
    have h1 := ha.2.1
    omega
  · rw [hv]
    simp only [List.map_cons, List.map_nil, ha.2.2 x y]

theorem op_bin (n r c : ℕ) (gs : List Gate) (hg : Good n r c gs) (op : GateOp) (a b : ℕ)
    (f g : (Fin n → Fin r) → (Fin n → Fin c) → Bool) (D : ℕ)
    (ha : Has n r c gs a f D) (hb : Has n r c gs b g D) :
    Ext n r c gs (gs ++ [⟨op, [a, b]⟩]) (nl ⟨op, [a, b]⟩).toNat ∧
    Has n r c (gs ++ [⟨op, [a, b]⟩]) (n * (r + c) + gs.length)
      (fun x y => op.eval [f x y, g x y]) (D + (nl ⟨op, [a, b]⟩).toNat) := by
  obtain ⟨hE, hk, hd, hv⟩ := op_gate n r c gs ⟨op, [a, b]⟩ hg
    (by
      intro i hi
      simp at hi
      rcases hi with h | h
      · rw [h]; exact ha.1
      · rw [h]; exact hb.1) (by simp)
  refine ⟨hE, hk, ?_, fun x y => ?_⟩
  · rw [hd]
    simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    have h1 := ha.2.1
    have h2 := hb.2.1
    omega
  · rw [hv]
    simp only [List.map_cons, List.map_nil, ha.2.2 x y, hb.2.2 x y]

theorem op_xor (n r c : ℕ) (gs : List Gate) (hg : Good n r c gs) (a b : ℕ)
    (f g : (Fin n → Fin r) → (Fin n → Fin c) → Bool) (D : ℕ)
    (ha : Has n r c gs a f D) (hb : Has n r c gs b g D) :
    ∃ gs' k, Ext n r c gs gs' 0 ∧ Has n r c gs' k (fun x y => xor (f x y) (g x y)) D := by
  obtain ⟨hE1, hH1⟩ := op_bin n r c gs hg (GateOp.mod 2) a b f g D ha hb
  rw [nl_mod2] at hE1 hH1
  have hH1' : Has n r c (gs ++ [⟨GateOp.mod 2, [a, b]⟩]) (n * (r + c) + gs.length)
      (fun x y => (GateOp.mod 2).eval [f x y, g x y]) D := hH1
  obtain ⟨hE2, hH2⟩ := op_un n r c _ hE1.1 GateOp.not _ _ D hH1'
  exact ⟨_, _, ext_trans hE1 hE2 rfl, has_congr hH2 (fun x y => ev_xnor_not _ _)⟩

theorem op_and (n r c : ℕ) (gs : List Gate) (hg : Good n r c gs) (a b : ℕ)
    (f g : (Fin n → Fin r) → (Fin n → Fin c) → Bool) (D : ℕ)
    (ha : Has n r c gs a f D) (hb : Has n r c gs b g D) :
    ∃ gs' k, Ext n r c gs gs' 1 ∧ Has n r c gs' k (fun x y => f x y && g x y) (D + 1) := by
  obtain ⟨hE1, hH1⟩ := op_bin n r c gs hg GateOp.and a b f g D ha hb
  rw [nl_and] at hE1 hH1
  exact ⟨_, _, hE1, has_congr hH1 (fun x y => ev_and _ _)⟩

theorem op_const (n r c : ℕ) (gs : List Gate) (hg : Good n r c gs) (b : Bool) :
    ∃ gs' k, Ext n r c gs gs' 0 ∧ Has n r c gs' k (fun _ _ => b) 0 := by
  have hn : nl ⟨bif b then GateOp.and else GateOp.or, []⟩ = false := by cases b <;> rfl
  obtain ⟨hE, hk, hd, hv⟩ := op_gate n r c gs ⟨bif b then GateOp.and else GateOp.or, []⟩ hg
    (by simp) (by simp)
  rw [hn] at hE hd
  refine ⟨_, _, hE, hk, ?_, fun x y => ?_⟩
  · rw [hd]; simp
  · rw [hv]; cases b <;> rfl

theorem rep_getD (W k : ℕ) : (List.replicate W 0).getD k 0 = 0 := by
  by_cases h : k < W
  · have hlt : k < (List.replicate W 0).length := by simpa using h
    rw [List.getD_eq_getElem _ _ hlt]
    simp
  · have hle : (List.replicate W 0).length ≤ k := by simpa using h
    exact List.getD_eq_default _ _ hle

theorem dep_input (n r c : ℕ) (gs : List Gate) (k : ℕ) (hk : k < n * (r + c)) :
    dep n r c gs k = 0 := by
  have h := dps_app_getD (n * (r + c)) [] gs k (by simpa using hk)
  rw [List.nil_append] at h
  have e : dep n r c gs k = (dps (n * (r + c)) gs).getD k 0 := rfl
  rw [e, h]
  exact rep_getD _ _

theorem val_input (n r c : ℕ) (gs : List Gate) (x : Fin n → Fin r) (y : Fin n → Fin c)
    (k : ℕ) (hk : k < n * (r + c)) :
    val n r c gs x y k = (inp n r c x y).getD k false := by
  have h := wr_app_getD [] gs (inp n r c x y) k (by rw [inp_length]; simpa using hk)
  rw [List.nil_append] at h
  exact h

theorem blk_lt (n r c : ℕ) (j : Fin n) (a : ℕ) (ha : a < r + c) :
    j.val * (r + c) + a < n * (r + c) := by
  have h1 : (j.val + 1) * (r + c) ≤ n * (r + c) := Nat.mul_le_mul_right _ j.isLt
  rw [Nat.succ_mul] at h1
  omega

theorem has_row (n r c : ℕ) (gs : List Gate) (j : Fin n) (a : ℕ) (ha : a < r) :
    Has n r c gs (j.val * (r + c) + a) (fun x _ => decide (a = (x j).val)) 0 := by
  have hlt := blk_lt n r c j a (by omega)
  refine ⟨by omega, ?_, fun x y => ?_⟩
  · rw [dep_input n r c gs _ hlt]
  · rw [val_input n r c gs x y _ hlt, inp_getD n r c x y j.val j.isLt a (by omega),
      one_getD_lt r c _ _ a ha]

theorem has_col (n r c : ℕ) (gs : List Gate) (j : Fin n) (b : ℕ) (hb : b < c) :
    Has n r c gs (j.val * (r + c) + (r + b)) (fun _ y => decide (b = (y j).val)) 0 := by
  have hlt := blk_lt n r c j (r + b) (by omega)
  refine ⟨by omega, ?_, fun x y => ?_⟩
  · rw [dep_input n r c gs _ hlt]
  · rw [val_input n r c gs x y _ hlt, inp_getD n r c x y j.val j.isLt (r + b) (by omega),
      one_getD_col r c _ _ b hb]

theorem xorForm (n r c : ℕ) (R : ℕ) (u : Fin R → Bool)
    (t : (Fin n → Fin r) → (Fin n → Fin c) → Fin R) (idx : ℕ → ℕ)
    (hw : ∀ (gs : List Gate) (a : ℕ), a < R →
      Has n r c gs (idx a) (fun x y => decide (a = (t x y).val)) 0) :
    ∀ m, m ≤ R → ∀ gs, Good n r c gs → ∃ gs' k, Ext n r c gs gs' 0 ∧
      Has n r c gs' k (fun x y => decide ((t x y).val < m) && u (t x y)) 0 := by
  intro m
  induction m with
  | zero =>
    intro _ gs hg
    obtain ⟨gs', k, hE, hH⟩ := op_const n r c gs hg false
    exact ⟨gs', k, hE, has_congr hH (fun x y => by simp)⟩
  | succ m ih =>
    intro hm gs hg
    obtain ⟨gs1, k1, hE1, hH1⟩ := ih (by omega) gs hg
    have hmR : m < R := by omega
    have hdec : ∀ x y, (t x y).val ≠ m →
        decide ((t x y).val < m + 1) = decide ((t x y).val < m) := by
      intro x y hx
      apply decide_eq_decide.mpr
      omega
    by_cases hu : u ⟨m, hmR⟩ = true
    · have hwm := hw gs1 m hmR
      obtain ⟨gs2, k2, hE2, hH2⟩ := op_xor n r c gs1 hE1.1 _ _ _ _ 0 hH1 hwm
      refine ⟨gs2, k2, ext_trans hE1 hE2 rfl, has_congr hH2 (fun x y => ?_)⟩
      by_cases hx : (t x y).val = m
      · have hxj : t x y = ⟨m, hmR⟩ := Fin.ext hx
        rw [hxj]
        simp [hu]
      · have h1 : decide (m = (t x y).val) = false := by simp [Ne.symm hx]
        rw [h1, hdec x y hx]
        simp
    · refine ⟨gs1, k1, hE1, has_congr hH1 (fun x y => ?_)⟩
      by_cases hx : (t x y).val = m
      · have hxj : t x y = ⟨m, hmR⟩ := Fin.ext hx
        have hu' : u (t x y) = false := by rw [hxj]; simpa using hu
        rw [hu']
        simp
      · rw [hdec x y hx]

theorem formF (n r c : ℕ) (R : ℕ) (u : Fin R → Bool)
    (t : (Fin n → Fin r) → (Fin n → Fin c) → Fin R) (idx : ℕ → ℕ)
    (hw : ∀ (gs : List Gate) (a : ℕ), a < R →
      Has n r c gs (idx a) (fun x y => decide (a = (t x y).val)) 0)
    (gs : List Gate) (hg : Good n r c gs) :
    ∃ gs' k, Ext n r c gs gs' 0 ∧ Has n r c gs' k (fun x y => u (t x y)) 0 := by
  obtain ⟨gs', k, hE, hH⟩ := xorForm n r c R u t idx hw R (le_refl R) gs hg
  exact ⟨gs', k, hE, has_congr hH (fun x y => by simp [(t x y).isLt])⟩

theorem rowF (n r c : ℕ) (u : Fin r → Bool) (j : Fin n) (gs : List Gate) (hg : Good n r c gs) :
    ∃ gs' k, Ext n r c gs gs' 0 ∧ Has n r c gs' k (fun x _ => u (x j)) 0 :=
  formF n r c r u (fun x _ => x j) (fun a => j.val * (r + c) + a)
    (fun gs a ha => has_row n r c gs j a ha) gs hg

theorem colF (n r c : ℕ) (v : Fin c → Bool) (j : Fin n) (gs : List Gate) (hg : Good n r c gs) :
    ∃ gs' k, Ext n r c gs gs' 0 ∧ Has n r c gs' k (fun _ y => v (y j)) 0 :=
  formF n r c c v (fun _ y => y j) (fun b => j.val * (r + c) + (r + b))
    (fun gs b hb => has_col n r c gs j b hb) gs hg

theorem blockCore (n r c : ℕ) (a0 a1 : Fin r → Bool) (b0 b1 : Fin c → Bool) (j : Fin n)
    (gs : List Gate) (hg : Good n r c gs) :
    ∃ gs' k0 k1, Ext n r c gs gs' 2 ∧
      Has n r c gs' k0 (fun x y => e0f (a0 (x j)) (b0 (y j))) 1 ∧
      Has n r c gs' k1 (fun x y => e1f (a0 (x j)) (a1 (x j)) (b0 (y j)) (b1 (y j))) 1 := by
  obtain ⟨g1, kA, E1, HA⟩ := rowF n r c a0 j gs hg
  obtain ⟨g2, kB, E2, HB⟩ := colF n r c b0 j g1 E1.1
  obtain ⟨g3, kP, E3, HP⟩ := op_and n r c g2 E2.1 _ _ _ _ 0 (has_mono E2 HA) HB
  obtain ⟨g4, kU1, E4, HU1⟩ := rowF n r c (fun t => !a0 t) j g3 E3.1
  obtain ⟨g5, kV1, E5, HV1⟩ := colF n r c (fun t => !b0 t) j g4 E4.1
  obtain ⟨g6, kL1, E6, HL1⟩ := op_xor n r c g5 E5.1 _ _ _ _ 0 (has_mono E5 HU1) HV1
  obtain ⟨g7, kU2, E7, HU2⟩ := rowF n r c (fun t => a0 t && a1 t) j g6 E6.1
  obtain ⟨g8, kV2, E8, HV2⟩ := colF n r c b1 j g7 E7.1
  obtain ⟨g9, kL2, E9, HL2⟩ := op_xor n r c g8 E8.1 _ _ _ _ 0 (has_mono E8 HU2) HV2
  have E69 : Ext n r c g6 g9 0 := ext_trans (ext_trans E7 E8 rfl) E9 rfl
  obtain ⟨g10, kP2, E10, HP2⟩ := op_and n r c g9 E9.1 _ _ _ _ 0 (has_mono E69 HL1) HL2
  have E510 : Ext n r c g5 g10 1 := ext_trans (ext_trans E6 E69 rfl) E10 rfl
  obtain ⟨g11, kE1, E11, HE1⟩ := op_xor n r c g10 E10.1 _ _ _ _ 1 HP2
    (has_weaken (has_mono E510 HV1) (by omega))
  have E311 : Ext n r c g3 g11 1 := ext_trans (ext_trans (ext_trans E4 E5 rfl) E510 rfl) E11 rfl
  have E011 : Ext n r c gs g11 2 := ext_trans (ext_trans (ext_trans E1 E2 rfl) E3 rfl) E311 rfl
  exact ⟨g11, kP, kE1, E011, has_mono E311 HP, HE1⟩

theorem condXor (n r c : ℕ) (gs : List Gate) (hg : Good n r c gs) (a k : ℕ)
    (f g : (Fin n → Fin r) → (Fin n → Fin c) → Bool) (D : ℕ)
    (ha : Has n r c gs a f D) (hk : Has n r c gs k g D) (d : Bool) :
    ∃ gs' k', Ext n r c gs gs' 0 ∧
      Has n r c gs' k' (fun x y => xor (f x y) (d && g x y)) D := by
  cases d
  · exact ⟨gs, a, ext_refl hg, has_congr ha (fun x y => by simp)⟩
  · obtain ⟨gs', k', hE, hH⟩ := op_xor n r c gs hg a k f g D ha hk
    exact ⟨gs', k', hE, has_congr hH (fun x y => by simp)⟩

theorem tapBit (n r c : ℕ) (gs : List Gate) (hg : Good n r c gs) (k0 k1 : ℕ)
    (f0 f1 : (Fin n → Fin r) → (Fin n → Fin c) → Bool)
    (h0 : Has n r c gs k0 f0 1) (h1 : Has n r c gs k1 f1 1) (K d0 d1 : Bool) :
    ∃ gs' k, Ext n r c gs gs' 0 ∧
      Has n r c gs' k (fun x y => xor (xor K (d0 && f0 x y)) (d1 && f1 x y)) 1 := by
  obtain ⟨g1, kc, E1, HC⟩ := op_const n r c gs hg K
  obtain ⟨g2, kx, E2, HX⟩ := condXor n r c g1 E1.1 kc k0 _ f0 1
    (has_weaken HC (by omega)) (has_mono E1 h0) d0
  obtain ⟨g3, ky, E3, HY⟩ := condXor n r c g2 E2.1 kx k1 _ f1 1 HX
    (has_mono (ext_trans E1 E2 rfl) h1) d1
  exact ⟨g3, ky, ext_trans (ext_trans E1 E2 rfl) E3 rfl, HY⟩

theorem collect (n r c : ℕ) {ι κ : Type} [DecidableEq ι] [Inhabited κ]
    (Rel : List Gate → ι → κ → Prop)
    (hmono : ∀ (gs gs' : List Gate) (m : ℕ) (i : ι) (k : κ),
      Ext n r c gs gs' m → Rel gs i k → Rel gs' i k)
    (P : List Gate → Prop)
    (hP : ∀ (gs gs' : List Gate) (m : ℕ), Ext n r c gs gs' m → P gs → P gs')
    (m0 : ℕ)
    (step : ∀ gs, Good n r c gs → P gs → ∀ i, ∃ gs' k, Ext n r c gs gs' m0 ∧ Rel gs' i k) :
    ∀ (l : List ι) (gs : List Gate), Good n r c gs → P gs →
      ∃ (gs' : List Gate) (t : ι → κ), Ext n r c gs gs' (m0 * l.length) ∧
        ∀ i ∈ l, Rel gs' i (t i) := by
  intro l
  induction l with
  | nil =>
    intro gs hg _
    exact ⟨gs, fun _ => default, ext_trans (ext_refl hg) (ext_refl hg) (by simp), by simp⟩
  | cons i l ih =>
    intro gs hg hp
    obtain ⟨g1, t1, E1, H1⟩ := ih gs hg hp
    obtain ⟨g2, k, E2, H2⟩ := step g1 E1.1 (hP _ _ _ E1 hp) i
    refine ⟨g2, fun i' => if i' = i then k else t1 i',
      ext_trans E1 E2 (by rw [List.length_cons, Nat.mul_succ]), ?_⟩
    intro i' hi'
    show Rel g2 i' (if i' = i then k else t1 i')
    by_cases h : i' = i
    · rw [if_pos h, h]; exact H2
    · rw [if_neg h]
      have hmem : i' ∈ l := by
        rcases List.mem_cons.mp hi' with h' | h'
        · exact absurd h' h
        · exact h'
      exact hmono _ _ _ _ _ E2 (H1 i' hmem)

theorem keysel : ∀ (k0 k1 k2 a0 a1 b0 b1 : Bool),
    xor (xor k2 ((xor k0 k2) && e0f a0 b0)) ((xor k1 k2) && e1f a0 a1 b0 b1)
      = (bif e0f a0 b0 then k0 else bif e1f a0 a1 b0 b1 then k1 else k2) := by
  decide

theorem key_selB (w : ℕ) (key : Fin 3 → Fin w → Bool) (a0 a1 b0 b1 : Bool) (b : Fin w) :
    key (selB a0 a1 b0 b1) b
      = (bif e0f a0 b0 then key 0 b else bif e1f a0 a1 b0 b1 then key 1 b else key 2 b) := by
  unfold selB
  cases e0f a0 b0 <;> cases e1f a0 a1 b0 b1 <;> rfl

theorem block (n r c w : ℕ) (key : Fin 3 → Fin w → Bool) (a0 a1 : Fin r → Bool)
    (b0 b1 : Fin c → Bool) (j : Fin n) (gs : List Gate) (hg : Good n r c gs) :
    ∃ (gs' : List Gate) (t : Fin w → ℕ), Ext n r c gs gs' 2 ∧
      ∀ b, Has n r c gs' (t b)
        (fun x y => key (selB (a0 (x j)) (a1 (x j)) (b0 (y j)) (b1 (y j))) b) 1 := by
  obtain ⟨g1, k0, k1, E1, H0, H1⟩ := blockCore n r c a0 a1 b0 b1 j gs hg
  obtain ⟨g2, t, E2, HT⟩ := collect n r c
    (fun (gs' : List Gate) (b : Fin w) (k : ℕ) => Has n r c gs' k
      (fun x y => key (selB (a0 (x j)) (a1 (x j)) (b0 (y j)) (b1 (y j))) b) 1)
    (fun gs gs' m i k hE h => has_mono hE h)
    (fun gs' => Has n r c gs' k0 (fun x y => e0f (a0 (x j)) (b0 (y j))) 1 ∧
      Has n r c gs' k1 (fun x y => e1f (a0 (x j)) (a1 (x j)) (b0 (y j)) (b1 (y j))) 1)
    (fun gs gs' m hE h => ⟨has_mono hE h.1, has_mono hE h.2⟩)
    0
    (fun gs' hg' hp b => by
      obtain ⟨g3, k, E3, H3⟩ := tapBit n r c gs' hg' k0 k1 _ _ hp.1 hp.2 (key 2 b)
        (xor (key 0 b) (key 2 b)) (xor (key 1 b) (key 2 b))
      exact ⟨g3, k, E3, has_congr H3 (fun x y =>
        (keysel _ _ _ _ _ _ _).trans (key_selB w key _ _ _ _ b).symm)⟩)
    (List.finRange w) g1 E1.1 ⟨H0, H1⟩
  exact ⟨g2, t, ext_trans E1 E2 (by simp), fun b => HT b (List.mem_finRange b)⟩

theorem valid : ∀ a0 a1 a2 b0 b1 b2 : Bool,
    ((a0 || a1) && (a0 || a2) && (a1 || a2) && (b0 || b1) && (b0 || b2) && (b1 || b2)) = true →
    (selB a0 a1 b0 b1 = 0 → a0 = true ∧ b0 = true) ∧
    (selB a0 a1 b0 b1 = 1 → a1 = true ∧ b1 = true) ∧
    (selB a0 a1 b0 b1 = 2 → a2 = true ∧ b2 = true) := by
  decide

theorem valid_bool (A B : Fin 3 → Bool)
    (h01 : A 0 = true ∨ A 1 = true) (h02 : A 0 = true ∨ A 2 = true)
    (h12 : A 1 = true ∨ A 2 = true)
    (g01 : B 0 = true ∨ B 1 = true) (g02 : B 0 = true ∨ B 2 = true)
    (g12 : B 1 = true ∨ B 2 = true) :
    A (selB (A 0) (A 1) (B 0) (B 1)) = true ∧ B (selB (A 0) (A 1) (B 0) (B 1)) = true := by
  have V := valid (A 0) (A 1) (A 2) (B 0) (B 1) (B 2) (by
    simp only [Bool.and_eq_true, Bool.or_eq_true]
    exact ⟨⟨⟨⟨⟨h01, h02⟩, h12⟩, g01⟩, g02⟩, g12⟩)
  rcases fin3_cover 0 1 2 (selB (A 0) (A 1) (B 0) (B 1)) (by decide) (by decide) (by decide)
    with h | h | h
  · rw [h]; exact V.1 h
  · rw [h]; exact V.2.1 h
  · rw [h]; exact V.2.2 h

theorem third_ex : ∀ i i' : Fin 3, i ≠ i' →
    ∃ i'' : Fin 3, ∀ k : Fin 3, k ≠ i → k ≠ i'' → k = i' := by
  decide

theorem upper (n r c w : ℕ) (rowOK : Fin r → Fin 3 → Prop) (colOK : Fin c → Fin 3 → Prop)
    (key : Fin 3 → Fin w → Bool)
    (hcov : ∀ x y, ∃ i, rowOK x i ∧ colOK y i)
    (hmiss : ∀ i, (∃ x, ¬ rowOK x i) ∧ (∃ y, ¬ colOK y i)) :
    ∃ (gs : List Gate) (tap : Fin n → Fin w → ℕ), Good n r c gs ∧
      (∀ j b, tap j b < n * (r + c) + gs.length) ∧
      (∀ (x : Fin n → Fin r) (y : Fin n → Fin c) (j : Fin n), ∃ i,
        rowOK (x j) i ∧ colOK (y j) i ∧
        ∀ b, (wr gs (inp n r c x y)).getD (tap j b) false = key i b) ∧
      gs.countP nl = 2 * n ∧
      ∀ j b, (dps (n * (r + c)) gs).getD (tap j b) 0 ≤ 1 := by
  classical
  have hrow2 : ∀ (x : Fin r) (i i' : Fin 3), i ≠ i' → ¬ rowOK x i → rowOK x i' := by
    intro x i i' hne hn
    obtain ⟨i'', h3⟩ := third_ex i i' hne
    obtain ⟨y, hy⟩ := (hmiss i'').2
    obtain ⟨k, hk1, hk2⟩ := hcov x y
    have hk : k = i' := h3 k (fun e => hn (by rw [← e]; exact hk1))
      (fun e => hy (by rw [← e]; exact hk2))
    rw [← hk]; exact hk1
  have hcol2 : ∀ (y : Fin c) (i i' : Fin 3), i ≠ i' → ¬ colOK y i → colOK y i' := by
    intro y i i' hne hn
    obtain ⟨i'', h3⟩ := third_ex i i' hne
    obtain ⟨x, hx⟩ := (hmiss i'').1
    obtain ⟨k, hk1, hk2⟩ := hcov x y
    have hk : k = i' := h3 k (fun e => hn (by rw [← e]; exact hk2))
      (fun e => hx (by rw [← e]; exact hk1))
    rw [← hk]; exact hk2
  have hror : ∀ (x : Fin r) (i i' : Fin 3), i ≠ i' →
      decide (rowOK x i) = true ∨ decide (rowOK x i') = true := by
    intro x i i' hne
    by_cases h : rowOK x i
    · exact Or.inl (decide_eq_true h)
    · exact Or.inr (decide_eq_true (hrow2 x i i' hne h))
  have hcor : ∀ (y : Fin c) (i i' : Fin 3), i ≠ i' →
      decide (colOK y i) = true ∨ decide (colOK y i') = true := by
    intro y i i' hne
    by_cases h : colOK y i
    · exact Or.inl (decide_eq_true h)
    · exact Or.inr (decide_eq_true (hcol2 y i i' hne h))
  have hgood0 : Good n r c [] := ⟨fun j hj => by simp at hj, fun g hg => by simp at hg⟩
  obtain ⟨gs, tap, hE, hT⟩ := collect n r c
    (fun (gs' : List Gate) (j : Fin n) (t : Fin w → ℕ) => ∀ b, Has n r c gs' (t b)
      (fun x y => key (selB (decide (rowOK (x j) 0)) (decide (rowOK (x j) 1))
        (decide (colOK (y j) 0)) (decide (colOK (y j) 1))) b) 1)
    (fun gs gs' m i k hE h b => has_mono hE (h b))
    (fun _ => True) (fun _ _ _ _ _ => trivial) 2
    (fun gs' hg' _ j => block n r c w key (fun t => decide (rowOK t 0))
      (fun t => decide (rowOK t 1)) (fun t => decide (colOK t 0))
      (fun t => decide (colOK t 1)) j gs' hg')
    (List.finRange n) [] hgood0 trivial
  obtain ⟨hg, ex, hex, hcnt⟩ := hE
  refine ⟨gs, tap, hg, fun j b => (hT j (List.mem_finRange j) b).1, ?_, ?_,
    fun j b => (hT j (List.mem_finRange j) b).2.1⟩
  · intro x y j
    have hv := valid_bool (fun i => decide (rowOK (x j) i)) (fun i => decide (colOK (y j) i))
      (hror (x j) 0 1 (by decide)) (hror (x j) 0 2 (by decide)) (hror (x j) 1 2 (by decide))
      (hcor (y j) 0 1 (by decide)) (hcor (y j) 0 2 (by decide)) (hcor (y j) 1 2 (by decide))
    exact ⟨_, of_decide_eq_true hv.1, of_decide_eq_true hv.2,
      fun b => (hT j (List.mem_finRange j) b).2.2 x y⟩
  · rw [hex, List.nil_append, hcnt, List.length_finRange]


end PEqualNP.Outside.L_meta_38505

theorem PEqualNP.Outside.L_meta_38505 :
  let nonlinear := fun (g : PEqualNP.CircuitLowerBounds.Gate) =>
    (g.inputs.length == 2) &&
      xor (xor (g.op.eval [false,false]) (g.op.eval [false,true]))
          (xor (g.op.eval [true,false]) (g.op.eval [true,true]))
  ∀ (n r c w : Nat) (rowOK : Fin r → Fin 3 → Prop) (colOK : Fin c → Fin 3 → Prop)
    (key : Fin 3 → Fin w → Bool), Function.Injective key →
    (∀ x y, ∃ i, rowOK x i ∧ colOK y i) →
    (∀ i, (∃ x, ¬ rowOK x i) ∧ (∃ y, ¬ colOK y i)) →
    let width := n*(r+c)
    let input := fun (x : Fin n → Fin r) (y : Fin n → Fin c) =>
      (List.ofFn (fun j : Fin n => PEqualNP.Represents.oneEach (x j) (y j))).flatten
    let fits := fun (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin n → Fin w → Nat) =>
      PEqualNP.MetaComplexity.NestedCover.ReadsBack width C ∧
      (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧
      (∀ j b, tap j b < width + C.gates.length) ∧
      ∀ x y j, ∃ i, rowOK (x j) i ∧ colOK (y j) i ∧
        ∀ b, (C.wires (input x y)).getD (tap j b) false = key i b
    let depths := fun (C : PEqualNP.CircuitLowerBounds.Circuit) =>
      C.gates.foldl (fun (ds : List Nat) g =>
        ds ++ [(g.inputs.map (fun i => ds.getD i 0)).foldr max 0 + (nonlinear g).toNat])
        (List.replicate width 0)
    (∃ C tap, fits C tap ∧ C.gates.countP nonlinear = 2*n ∧
      ∀ j b, (depths C).getD (tap j b) 0 ≤ 1) ∧
    ∀ C tap, fits C tap → 2*n ≤ C.gates.countP nonlinear := by
  intro nonlinear n r c w rowOK colOK key hinj hcov hmiss width input fits depths
  refine ⟨?_, ?_⟩
  · obtain ⟨gs, tap, hg, htap, hfit, hcnt, hdep⟩ :=
      PEqualNP.Outside.L_meta_38505.upper n r c w rowOK colOK key hcov hmiss
    exact ⟨⟨gs, 0⟩, tap, ⟨hg.1, hg.2, htap, hfit⟩, hcnt, hdep⟩
  · intro C tap hf
    exact PEqualNP.Outside.L_meta_38505.lower n r c w rowOK colOK key hinj hmiss C.gates tap
      hf.2.1 hf.2.2.2
