import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

namespace PEqualNP.Outside.L_meta_25464

private theorem wires_append (gs hs : List Gate) (out : ℕ) (x : List Bool) :
    (⟨gs ++ hs, out⟩ : Circuit).wires x =
      hs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        ((⟨gs, 0⟩ : Circuit).wires x) := by
  simp [Circuit.wires, List.foldl_append]

private theorem wires_length (gs : List Gate) (out : ℕ) (x : List Bool) :
    ((⟨gs, out⟩ : Circuit).wires x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [Circuit.wires]
  | append_singleton gs g ih =>
    simp [Circuit.wires, List.foldl_append] at ih ⊢
    omega

private theorem wires_getD_prefix (gs hs : List Gate) (x : List Bool) (i : ℕ)
    (hi : i < x.length + gs.length) :
    ((⟨gs ++ hs, 0⟩ : Circuit).wires x).getD i false =
      ((⟨gs, 0⟩ : Circuit).wires x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    have hlen : i < ((⟨gs ++ hs, 0⟩ : Circuit).wires x).length := by
      rw [wires_length, List.length_append]; omega
    rw [← List.append_assoc, wires_append]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlen, ← List.getD_eq_getElem?_getD]
    exact ih

private theorem oneEach_length {r c : ℕ} (u : Fin r) (v : Fin c) :
    (oneEach u v).length = r + c := by
  simp [oneEach]

private theorem oneEach_getD_left {r c : ℕ} (u : Fin r) (v : Fin c) (i : ℕ) (hi : i < r) :
    (oneEach u v).getD i false = decide (u.val = i) := by
  simp [oneEach, List.getD_eq_getElem?_getD, List.getElem?_append_left, hi, Fin.ext_iff, eq_comm]

private theorem oneEach_getD_right {r c : ℕ} (u : Fin r) (v : Fin c) (j : ℕ) (hj : j < c) :
    (oneEach u v).getD (r + j) false = decide (v.val = j) := by
  simp [oneEach, List.getD_eq_getElem?_getD, hj, Fin.ext_iff, eq_comm]

private theorem list_any_congr {α : Type*} {l : List α} {p q : α → Bool}
    (h : ∀ x ∈ l, p x = q x) : l.any p = l.any q := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [h a List.mem_cons_self, ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

private theorem map_gates_sim (L1 M : ℕ) (ρ : ℕ → ℕ) (gs : List Gate) (x W2 : List Bool)
    (hxlen : x.length = L1)
    (hM : W2.length + gs.length ≤ M)
    (hρ_in : ∀ i < L1, (ρ i < W2.length ∧ W2.getD (ρ i) false = x.getD i false) ∨
                       (M ≤ ρ i ∧ x.getD i false = false))
    (hρ_ge : ∀ i, L1 ≤ i → ρ i = i - L1 + W2.length) :
    ∀ (i : ℕ),
      ((⟨gs.map (fun g => ⟨g.op, g.inputs.map ρ⟩), 0⟩ : Circuit).wires W2).getD (ρ i) false =
        ((⟨gs, 0⟩ : Circuit).wires x).getD i false := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro i
    simp only [List.map_nil, Circuit.wires, List.foldl_nil]
    by_cases hi : i < L1
    · rcases hρ_in i hi with ⟨_, heq⟩ | ⟨hge, hfalse⟩
      · exact heq
      · have : W2.length ≤ ρ i := by simp at hM; omega
        rw [hfalse, List.getD_eq_getElem?_getD, List.getElem?_eq_none this]; rfl
    · have h1 : L1 ≤ i := by omega
      have h2 : W2.length ≤ ρ i := by rw [hρ_ge i h1]; omega
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : x.length ≤ i),
        List.getElem?_eq_none h2]
  | append_singleton gs g ih =>
    intro i
    have hM' : W2.length + gs.length ≤ M := by simp at hM; omega
    have ih' := ih hM'
    set gs' : List Gate := gs.map (fun g => ⟨g.op, g.inputs.map ρ⟩)
    set g' : Gate := ⟨g.op, g.inputs.map ρ⟩
    have hmap : (gs ++ [g]).map (fun g => ⟨g.op, g.inputs.map ρ⟩) = gs' ++ [g'] := by
      simp [gs', g']
    rw [hmap, wires_append, wires_append]
    simp only [List.foldl_cons, List.foldl_nil]
    set W1 := (⟨gs, 0⟩ : Circuit).wires x
    set W2' := (⟨gs', 0⟩ : Circuit).wires W2
    have hW1len : W1.length = L1 + gs.length := by rw [wires_length, hxlen]
    have hW2'len : W2'.length = W2.length + gs.length := by
      rw [wires_length]; simp [gs']
    have hval_eq : g'.op.eval (g'.inputs.map fun k => W2'.getD k false) =
        g.op.eval (g.inputs.map fun k => W1.getD k false) := by
      simp only [g', List.map_map]
      congr 1
      apply List.map_congr_left
      intro k _
      exact ih' k
    rw [hval_eq]
    by_cases hi_lt : i < L1 + gs.length
    · by_cases h1 : i < L1
      · rcases hρ_in i h1 with ⟨hρlt, _⟩ | ⟨hρge, hfalse⟩
        · have hL : ∀ (l : List Bool) (a : Bool) (k : ℕ), k < l.length →
              (l ++ [a]).getD k false = l.getD k false := by
            intro l a k hk
            rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hk, ← List.getD_eq_getElem?_getD]
          rw [hL W2' _ (ρ i) (by omega), hL W1 _ i (by omega)]
          exact ih' i
        · have hW2_ge : (W2' ++ [g.op.eval (g.inputs.map fun k => W1.getD k false)]).length ≤ ρ i := by
            simp only [List.length_append, List.length_singleton, hW2'len]
            simp at hM; omega
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hW2_ge]
          simp only [Option.getD_none]
          have hW1_get : (W1 ++ [g.op.eval (g.inputs.map fun k => W1.getD k false)]).getD i false = x.getD i false := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : i < W1.length),
              ← List.getD_eq_getElem?_getD]
            have hpre := wires_getD_prefix [] gs x i (by simpa [hxlen] using h1)
            simpa [W1, Circuit.wires] using hpre
          rw [hW1_get, hfalse]
      · have hρi_lt : ρ i < W2'.length := by rw [hρ_ge i (by omega)]; omega
        have hL : ∀ (l : List Bool) (a : Bool) (k : ℕ), k < l.length →
            (l ++ [a]).getD k false = l.getD k false := by
          intro l a k hk
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hk, ← List.getD_eq_getElem?_getD]
        rw [hL W2' _ (ρ i) hρi_lt, hL W1 _ i (by omega)]
        exact ih' i
    · by_cases hi_eq : i = L1 + gs.length
      · subst hi_eq
        have hρi_eq : ρ (L1 + gs.length) = W2'.length := by
          rw [hρ_ge _ (by omega)]; omega
        rw [hρi_eq, ← hW1len]
        simp [List.getD_eq_getElem?_getD]
      · have hρi_gt : W2'.length + 1 ≤ ρ i := by
          rw [hρ_ge i (by omega)]; omega
        simp [List.getD_eq_getElem?_getD,
          List.getElem?_eq_none (by simp [hW1len]; omega : (W1 ++ [_]).length ≤ i),
          List.getElem?_eq_none (by simp [hW2'len]; omega : (W2' ++ [_]).length ≤ ρ i)]

private def orFold (base : ℕ) : ℕ → List Gate → List ℕ → List Gate × ℕ
  | acc, gs, [] => (gs, acc)
  | acc, gs, w :: ws => orFold base (base + gs.length) (gs ++ [⟨.or, [acc, w]⟩]) ws

private theorem orFold_spec (base : ℕ) (ws : List ℕ) :
    ∀ (acc : ℕ) (gs : List Gate),
      acc < base + gs.length →
      (∀ w ∈ ws, w < base + gs.length) →
      (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) →
      let (gs', out) := orFold base acc gs ws
      gs'.length = gs.length + ws.length ∧
      (∀ g ∈ gs', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      out < base + gs'.length ∧
      ∀ (W : List Bool), W.length = base →
        ((⟨gs', 0⟩ : Circuit).wires W).getD out false =
          (((⟨gs, 0⟩ : Circuit).wires W).getD acc false ||
            ws.any (fun i => ((⟨gs, 0⟩ : Circuit).wires W).getD i false)) := by
  induction ws with
  | nil =>
    intro acc gs hacc _ hmono
    simp only [orFold, List.length_nil, add_zero, List.any_nil, Bool.or_false]
    exact ⟨trivial, hmono, hacc, fun _ _ => trivial⟩
  | cons w ws ih =>
    intro acc gs hacc hws hmono
    have hw : w < base + gs.length := hws w (List.mem_cons_self)
    let gNew : Gate := ⟨.or, [acc, w]⟩
    let gs1 := gs ++ [gNew]
    have hgs1_len : gs1.length = gs.length + 1 := by simp [gs1]
    have hmono1 : ∀ g ∈ gs1, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
      intro g hg
      rw [List.mem_append] at hg
      rcases hg with hg | hg
      · exact hmono g hg
      · simp only [List.mem_singleton] at hg; subst hg; simp [gNew]
    have hrec := ih (base + gs.length) gs1 (by omega)
      (fun w' hw' => by have := hws w' (List.mem_cons_of_mem _ hw'); omega) hmono1
    simp only [orFold]
    rcases hor : orFold base (base + gs.length) gs1 ws with ⟨gs', out⟩
    rw [hor] at hrec
    rcases hrec with ⟨hlen', hmono', hout', heval'⟩
    refine ⟨by simp only [List.length_cons]; omega, hmono', hout', ?_⟩
    intro W hWlen
    rw [heval' W hWlen]
    have hstep_val : ((⟨gs1, 0⟩ : Circuit).wires W).getD (base + gs.length) false =
        (((⟨gs, 0⟩ : Circuit).wires W).getD acc false || ((⟨gs, 0⟩ : Circuit).wires W).getD w false) := by
      have hlen_gs : ((⟨gs, 0⟩ : Circuit).wires W).length = base + gs.length := by
        rw [wires_length, hWlen]
      simp only [gs1, gNew, wires_append, List.foldl_cons, List.foldl_nil, GateOp.eval,
        List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
      rw [← hlen_gs, List.getD_eq_getElem?_getD]
      simp
    have hany_eq : ws.any (fun i => ((⟨gs1, 0⟩ : Circuit).wires W).getD i false) =
        ws.any (fun i => ((⟨gs, 0⟩ : Circuit).wires W).getD i false) := by
      apply list_any_congr
      intro i hi
      exact wires_getD_prefix gs [gNew] W i (by rw [hWlen]; exact hws i (List.mem_cons_of_mem _ hi))
    rw [hstep_val, hany_eq]
    simp only [List.any_cons, Bool.or_assoc]

private def orChain (base : ℕ) : List ℕ → List Gate × ℕ
  | [] => ([], 0)
  | w :: ws => orFold base w [] ws

private theorem orChain_spec (base : ℕ) (l : List ℕ) (hne : l ≠ [])
    (hlt : ∀ w ∈ l, w < base) :
    let (gs, out) := orChain base l
    gs.length = l.length - 1 ∧
    (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
    out < base + gs.length ∧
    ∀ (W : List Bool), W.length = base →
      ((⟨gs, 0⟩ : Circuit).wires W).getD out false = l.any (fun i => W.getD i false) := by
  cases l with
  | nil => contradiction
  | cons w ws =>
    simp only [orChain]
    have h := orFold_spec base ws w [] (by simpa using hlt w (List.mem_cons_self))
      (fun w' hw' => by simpa using hlt w' (List.mem_cons_of_mem _ hw')) (by simp)
    rcases hor : orFold base w [] ws with ⟨gs, out⟩
    rw [hor] at h
    rcases h with ⟨hlen, hmono, hout, heval⟩
    refine ⟨by simp [hlen], hmono, hout, fun W hWlen => ?_⟩
    simpa [Circuit.wires, List.any_cons] using heval W hWlen

private def fiberList (off : ℕ) {a b : ℕ} (f : Fin a → Fin b) (k : ℕ) : List ℕ :=
  (List.finRange a).filterMap (fun u => if (f u).val = k then some (off + u.val) else none)

private theorem fiberList_sum {a b : ℕ} (off : ℕ) (f : Fin a → Fin b) (l : List (Fin a)) :
    ∑ k ∈ Finset.range b, (l.filterMap (fun u => if (f u).val = k then some (off + u.val) else none)).length = l.length := by
  induction l with
  | nil => simp
  | cons x t ih =>
    have hsplit : ∀ k, ((x :: t).filterMap (fun u => if (f u).val = k then some (off + u.val) else none)).length =
        (if (f x).val = k then 1 else 0) +
        (t.filterMap (fun u => if (f u).val = k then some (off + u.val) else none)).length := by
      intro k; by_cases h : (f x).val = k <;> simp [h, Nat.add_comm]
    simp_rw [hsplit, Finset.sum_add_distrib, ih]
    have hmem : (f x).val ∈ Finset.range b := Finset.mem_range.mpr (f x).isLt
    simp [Finset.sum_ite_eq, hmem, Nat.add_comm]

private def buildFibers (base0 off : ℕ) {a b : ℕ} (f : Fin a → Fin b) : ℕ → List Gate × List ℕ
  | 0 => ([], [])
  | k + 1 =>
    let (gs, ws) := buildFibers base0 off f k
    let (gsK, wK) := orChain (base0 + gs.length) (fiberList off f k)
    (gs ++ gsK, ws ++ [wK])

private theorem buildFibers_spec (base0 off : ℕ) {a b : ℕ} (f : Fin a → Fin b)
    (hf : Function.Surjective f) (hoff : off + a ≤ base0) (k : ℕ) (hk : k ≤ b) :
    let (gs, ws) := buildFibers base0 off f k
    gs.length + k = ∑ i ∈ Finset.range k, (fiberList off f i).length ∧
    ws.length = k ∧
    (∀ w ∈ ws, w < base0 + gs.length) ∧
    (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
    ∀ (W : List Bool), W.length = base0 →
      ∀ (i : ℕ), i < k →
        ((⟨gs, 0⟩ : Circuit).wires W).getD (ws.getD i 0) false =
          (fiberList off f i).any (fun idx => W.getD idx false) := by
  induction k with
  | zero => simp [buildFibers]
  | succ k ih =>
    have ih' := ih (by omega)
    rcases hbf : buildFibers base0 off f k with ⟨gs, ws⟩
    rw [hbf] at ih'
    rcases ih' with ⟨hlen_gs, hlen_ws, hws_lt, hmono_gs, heval_gs⟩
    obtain ⟨u0, hu0⟩ := hf ⟨k, by omega⟩
    have hne : fiberList off f k ≠ [] := by
      intro hemp
      have hmem : off + u0.val ∈ fiberList off f k := by
        simp only [fiberList, List.mem_filterMap, List.mem_finRange, true_and]
        exact ⟨u0, by simp [hu0]⟩
      rw [hemp] at hmem; simp at hmem
    have hlt : ∀ w ∈ fiberList off f k, w < base0 + gs.length := by
      intro w hw
      simp only [fiberList, List.mem_filterMap, List.mem_finRange, true_and] at hw
      rcases hw with ⟨u, hu⟩
      split_ifs at hu with h
      · simp at hu; omega
    have hpos : 1 ≤ (fiberList off f k).length := List.length_pos_of_ne_nil hne
    have hor := orChain_spec (base0 + gs.length) (fiberList off f k) hne hlt
    rcases hoc : orChain (base0 + gs.length) (fiberList off f k) with ⟨gsK, wK⟩
    rw [hoc] at hor
    rcases hor with ⟨hlen_K, hmono_K, hwK_lt, heval_K⟩
    simp only [buildFibers, hbf, hoc]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [List.length_append, Finset.sum_range_succ]; omega
    · simp [hlen_ws]
    · intro w hw
      rw [List.mem_append, List.mem_singleton] at hw
      rcases hw with hw | rfl
      · have := hws_lt w hw; rw [List.length_append]; omega
      · rw [List.length_append]; omega
    · intro g hg
      rw [List.mem_append] at hg
      rcases hg with hg | hg
      · exact hmono_gs g hg
      · exact hmono_K g hg
    · intro W hWlen i hi
      by_cases hik : i < k
      · have hget_w : (ws ++ [wK]).getD i 0 = ws.getD i 0 := by
          simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : i < ws.length)]
        rw [hget_w]
        have hw_lt : ws.getD i 0 < W.length + gs.length := by
          rw [hWlen]
          have hmem : ws.getD i 0 ∈ ws := by
            rw [show ws.getD i 0 = ws[i] by simp [List.getD_eq_getElem?_getD, show i < ws.length by omega]]
            exact List.getElem_mem _
          exact hws_lt _ hmem
        rw [wires_getD_prefix gs gsK W _ hw_lt]
        exact heval_gs W hWlen i hik
      · have hieq : i = k := by omega
        subst hieq
        have hget_w : (ws ++ [wK]).getD i 0 = wK := by
          rw [← hlen_ws, List.getD_eq_getElem?_getD]; simp
        rw [hget_w]
        set W1 := (⟨gs, 0⟩ : Circuit).wires W
        have hW1len : W1.length = base0 + gs.length := by rw [wires_length, hWlen]
        have hwa : (⟨gs ++ gsK, 0⟩ : Circuit).wires W = (⟨gsK, 0⟩ : Circuit).wires W1 := by
          simp [W1, Circuit.wires, List.foldl_append]
        rw [hwa, heval_K W1 hW1len]
        apply list_any_congr
        intro idx hidx
        have hidx_lt : idx < base0 := by
          simp only [fiberList, List.mem_filterMap, List.mem_finRange, true_and] at hidx
          rcases hidx with ⟨u, hu⟩
          split_ifs at hu with h
          · simp at hu; omega
        have h1 := wires_getD_prefix [] gs W idx (by simpa [hWlen] using hidx_lt)
        simpa [W1, Circuit.wires] using h1

end PEqualNP.Outside.L_meta_25464

open PEqualNP.Outside.L_meta_25464

theorem PEqualNP.Outside.L_meta_25464 : (∀ (n m n0 m0 s t : ℕ) (Q : Fin n0 → Fin m0 → Bool) (f : Fin n → Fin n0) (g : Fin m → Fin m0), Function.Surjective f → Function.Surjective g → (PEqualNP.Represents.RepSizeAtMost Q s → PEqualNP.Represents.RepSizeAtMost (fun (u : Fin n) (v : Fin m) => Q (f u) (g v)) (s + (n - n0) + (m - m0))) ∧ ((∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ t ∧ PEqualNP.Represents.Represents (fun (u : Fin n) (v : Fin m) => Q (f u) (g v)) C) → ∃ C' : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C' ∧ C'.size ≤ t ∧ PEqualNP.Represents.Represents Q C')) := by
  intro n m n0 m0 s t Q f g hf hg
  constructor
  ·
    rintro ⟨C, hmonoC, hsizeC, hrepC⟩
    have hbfL := buildFibers_spec (n + m) 0 f hf (by omega) n0 le_rfl
    rcases hL : buildFibers (n + m) 0 f n0 with ⟨gsL, wsL⟩
    rw [hL] at hbfL
    rcases hbfL with ⟨hlen_gsL, hlen_wsL, hwsL_lt, hmono_gsL, heval_gsL⟩
    have hsumL : ∑ i ∈ Finset.range n0, (fiberList 0 f i).length = n := by
      simpa [fiberList] using fiberList_sum 0 f (List.finRange n)
    have hgsL_len : gsL.length = n - n0 := by omega
    have hbfR := buildFibers_spec (n + m + gsL.length) n g hg (by omega) m0 le_rfl
    rcases hR : buildFibers (n + m + gsL.length) n g m0 with ⟨gsR, wsR⟩
    rw [hR] at hbfR
    rcases hbfR with ⟨hlen_gsR, hlen_wsR, hwsR_lt, hmono_gsR, heval_gsR⟩
    have hsumR : ∑ i ∈ Finset.range m0, (fiberList n g i).length = m := by
      simpa [fiberList] using fiberList_sum n g (List.finRange m)
    have hgsR_len : gsR.length = m - m0 := by omega
    let base2 := n + m + gsL.length + gsR.length
    let ρ : ℕ → ℕ := fun i =>
      if i < n0 then wsL.getD i 0
      else if i < n0 + m0 then wsR.getD (i - n0) 0
      else i - (n0 + m0) + base2
    let gsC : List Gate := C.gates.map (fun gt => ⟨gt.op, gt.inputs.map ρ⟩)
    refine ⟨(⟨gsL ++ gsR ++ gsC, ρ C.output⟩ : Circuit), ?_, ?_, ?_⟩
    · intro gt hgt
      simp only [List.mem_append, gsC, List.mem_map] at hgt
      rcases hgt with (h | h) | ⟨gt0, hgt0, rfl⟩
      · exact hmono_gsL gt h
      · exact hmono_gsR gt h
      · have ⟨hop, hlen⟩ := hmonoC gt0 hgt0
        exact ⟨hop, by simpa using hlen⟩
    · simp only [Circuit.size, List.length_append, gsC, List.length_map]
      simp only [Circuit.size] at hsizeC
      omega
    · intro u v
      simp only [Circuit.eval]
      set W1 := (⟨gsL, 0⟩ : Circuit).wires (oneEach u v)
      have hW1len : W1.length = n + m + gsL.length := by rw [wires_length, oneEach_length]
      set W2 := (⟨gsL ++ gsR, 0⟩ : Circuit).wires (oneEach u v)
      have hW2eq : W2 = (⟨gsR, 0⟩ : Circuit).wires W1 := by
        simp [W2, W1, Circuit.wires, List.foldl_append]
      have hW2len : W2.length = base2 := by rw [wires_length, oneEach_length, List.length_append]; omega
      have hwa : (⟨gsL ++ gsR ++ gsC, ρ C.output⟩ : Circuit).wires (oneEach u v) =
          (⟨gsC, 0⟩ : Circuit).wires W2 := by
        simp [W2, Circuit.wires, List.foldl_append]
      rw [hwa]
      have hsim := map_gates_sim (n0 + m0) (base2 + C.gates.length) ρ C.gates
        (oneEach (f u) (g v)) W2 (oneEach_length (f u) (g v)) (by rw [hW2len])
        (fun i hi => by
          left
          by_cases hi1 : i < n0
          · have hρ : ρ i = wsL.getD i 0 := by simp [ρ, hi1]
            rw [hρ]
            have hmem : wsL.getD i 0 ∈ wsL := by
              rw [show wsL.getD i 0 = wsL[i] by simp [List.getD_eq_getElem?_getD, show i < wsL.length by omega]]
              exact List.getElem_mem _
            have hlt : wsL.getD i 0 < n + m + gsL.length := hwsL_lt _ hmem
            refine ⟨by rw [hW2len]; omega, ?_⟩
            rw [show W2.getD (wsL.getD i 0) false = W1.getD (wsL.getD i 0) false from
              wires_getD_prefix gsL gsR (oneEach u v) _ (by rw [oneEach_length]; exact hlt)]
            rw [heval_gsL (oneEach u v) (oneEach_length u v) i hi1]
            rw [oneEach_getD_left (f u) (g v) i hi1]
            apply Bool.eq_iff_iff.mpr
            simp only [fiberList, List.any_eq_true, List.mem_filterMap, List.mem_finRange, true_and,
              decide_eq_true_eq, zero_add]
            constructor
            · rintro ⟨w, ⟨u', hu'⟩, hw⟩
              split_ifs at hu' with h
              · simp at hu'; subst hu'
                rw [oneEach_getD_left u v u'.val u'.isLt] at hw
                simp at hw
                have huu : u = u' := Fin.ext hw
                subst huu; exact h
            · intro hfu
              exact ⟨u.val, ⟨u, by simp [hfu]⟩, by rw [oneEach_getD_left u v u.val u.isLt]; simp⟩
          · have hi2 : i < n0 + m0 := hi
            have hρ : ρ i = wsR.getD (i - n0) 0 := by simp [ρ, hi1, hi2]
            rw [hρ]
            have hmem : wsR.getD (i - n0) 0 ∈ wsR := by
              rw [show wsR.getD (i - n0) 0 = wsR[i - n0] by simp [List.getD_eq_getElem?_getD, show i - n0 < wsR.length by omega]]
              exact List.getElem_mem _
            have hlt : wsR.getD (i - n0) 0 < base2 := hwsR_lt _ hmem
            refine ⟨by rw [hW2len]; exact hlt, ?_⟩
            rw [hW2eq, heval_gsR W1 hW1len (i - n0) (by omega)]
            have hsub : n0 + (i - n0) = i := by omega
            rw [← hsub, oneEach_getD_right (f u) (g v) (i - n0) (by omega)]
            apply Bool.eq_iff_iff.mpr
            simp only [fiberList, List.any_eq_true, List.mem_filterMap, List.mem_finRange, true_and,
              decide_eq_true_eq]
            constructor
            · rintro ⟨w, ⟨v', hv'⟩, hw⟩
              split_ifs at hv' with h
              · simp at hv'; subst hv'
                have hw1 : W1.getD (n + v'.val) false = (oneEach u v).getD (n + v'.val) false := by
                  have hpre := wires_getD_prefix [] gsL (oneEach u v) (n + v'.val) (by rw [oneEach_length]; omega)
                  simpa [W1, Circuit.wires] using hpre
                rw [hw1, oneEach_getD_right u v v'.val v'.isLt] at hw
                simp at hw
                have hvv : v = v' := Fin.ext hw
                subst hvv; simp at h; exact h
            · intro hgv
              refine ⟨n + v.val, ⟨v, by simp [hgv]⟩, ?_⟩
              have hw1 : W1.getD (n + v.val) false = (oneEach u v).getD (n + v.val) false := by
                have hpre := wires_getD_prefix [] gsL (oneEach u v) (n + v.val) (by rw [oneEach_length]; omega)
                simpa [W1, Circuit.wires] using hpre
              rw [hw1, oneEach_getD_right u v v.val v.isLt]; simp)
        (fun i hi => by
          have h1 : ¬ i < n0 := by omega
          have h2 : ¬ i < n0 + m0 := by omega
          simp [ρ, h1, h2, hW2len])
      rw [hsim C.output]
      exact hrepC (f u) (g v)
  ·
    rintro ⟨C, hfanC, hsizeC, hrepC⟩
    classical
    let fi : Fin n0 → Fin n := fun u0 => Classical.choose (hf u0)
    let gi : Fin m0 → Fin m := fun v0 => Classical.choose (hg v0)
    have hfi : ∀ u0, f (fi u0) = u0 := fun u0 => Classical.choose_spec (hf u0)
    have hgi : ∀ v0, g (gi v0) = v0 := fun v0 => Classical.choose_spec (hg v0)
    let bad := n0 + m0 + C.gates.length
    let σ : ℕ → ℕ := fun i =>
      if h1 : i < n then
        if h2 : ∃ u0 : Fin n0, (fi u0).val = i then (Classical.choose h2).val else bad
      else if h3 : i < n + m then
        if h4 : ∃ v0 : Fin m0, (gi v0).val = i - n then n0 + (Classical.choose h4).val else bad
      else i - (n + m) + (n0 + m0)
    let gs' : List Gate := C.gates.map (fun gt => ⟨gt.op, gt.inputs.map σ⟩)
    refine ⟨(⟨gs', σ C.output⟩ : Circuit), ?_, ?_, ?_⟩
    · intro gt hgt
      simp only [gs', List.mem_map] at hgt
      rcases hgt with ⟨gt0, hgt0, rfl⟩
      have ⟨hop, hlen⟩ := hfanC gt0 hgt0
      exact ⟨hop, by simpa using hlen⟩
    · simp only [Circuit.size, gs', List.length_map]
      exact hsizeC
    · intro u0 v0
      simp only [Circuit.eval]
      have hsim := map_gates_sim (n + m) bad σ C.gates (oneEach (fi u0) (gi v0)) (oneEach u0 v0)
        (oneEach_length (fi u0) (gi v0)) (by rw [oneEach_length])
        (fun i hi => by
          by_cases h1 : i < n
          · by_cases h2 : ∃ u' : Fin n0, (fi u').val = i
            · left
              have hσ : σ i = (Classical.choose h2).val := by simp [σ, h1, h2]
              rw [hσ]
              set u' := Classical.choose h2
              have hu' : (fi u').val = i := Classical.choose_spec h2
              refine ⟨by rw [oneEach_length]; omega, ?_⟩
              rw [oneEach_getD_left u0 v0 u'.val u'.isLt, oneEach_getD_left (fi u0) (gi v0) i h1]
              apply Bool.eq_iff_iff.mpr
              simp only [decide_eq_true_eq]
              constructor
              · intro heq; have h0 : u0 = u' := Fin.ext heq; subst h0; exact hu'
              · intro heq
                have hfi_eq : fi u0 = fi u' := Fin.ext (heq.trans hu'.symm)
                have := congrArg f hfi_eq
                rw [hfi, hfi] at this
                exact congrArg Fin.val this
            · right
              have hσ : σ i = bad := by simp [σ, h1, h2]
              rw [hσ, oneEach_getD_left (fi u0) (gi v0) i h1]
              refine ⟨le_rfl, ?_⟩
              simp only [decide_eq_false_iff_not]
              intro heq; exact h2 ⟨u0, heq⟩
          · have h3 : i < n + m := hi
            by_cases h4 : ∃ v' : Fin m0, (gi v').val = i - n
            · left
              have hσ : σ i = n0 + (Classical.choose h4).val := by simp [σ, h1, h3, h4]
              rw [hσ]
              set v' := Classical.choose h4
              have hv' : (gi v').val = i - n := Classical.choose_spec h4
              refine ⟨by rw [oneEach_length]; omega, ?_⟩
              have hsub : n + (i - n) = i := by omega
              rw [oneEach_getD_right u0 v0 v'.val v'.isLt, ← hsub,
                  oneEach_getD_right (fi u0) (gi v0) (i - n) (by omega)]
              apply Bool.eq_iff_iff.mpr
              simp only [decide_eq_true_eq]
              constructor
              · intro heq; have h0 : v0 = v' := Fin.ext heq; subst h0; exact hv'
              · intro heq
                have hgi_eq : gi v0 = gi v' := Fin.ext (heq.trans hv'.symm)
                have := congrArg g hgi_eq
                rw [hgi, hgi] at this
                exact congrArg Fin.val this
            · right
              have hσ : σ i = bad := by simp [σ, h1, h3, h4]
              have hsub : n + (i - n) = i := by omega
              rw [hσ, ← hsub, oneEach_getD_right (fi u0) (gi v0) (i - n) (by omega)]
              refine ⟨le_rfl, ?_⟩
              simp only [decide_eq_false_iff_not]
              intro heq; exact h4 ⟨v0, heq⟩)
        (fun i hi => by
          have h1 : ¬ i < n := by omega
          have h3 : ¬ i < n + m := by omega
          simp [σ, h1, h3, oneEach_length])
      have hres := hsim C.output
      change ((⟨gs', σ C.output⟩ : Circuit).wires (oneEach u0 v0)).getD (σ C.output) false =
        C.eval (oneEach (fi u0) (gi v0)) at hres
      rw [hres, hrepC (fi u0) (gi v0)]; dsimp only; rw [hfi, hgi]
