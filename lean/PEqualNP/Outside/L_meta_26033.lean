import Mathlib
import PEqualNP.Defs


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

namespace PEqualNP.Outside.L_meta_26033_aux.Compression

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

private theorem compress (n m n0 m0 s : ℕ) (Q : Fin n0 → Fin m0 → Bool) (f : Fin n → Fin n0) (g : Fin m → Fin m0)
    (hf : Function.Surjective f) (hg : Function.Surjective g) :
    RepSizeAtMost Q s → RepSizeAtMost (fun u v => Q (f u) (g v)) (s+(n-n0)+(m-m0)) := by
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
end PEqualNP.Outside.L_meta_26033_aux.Compression


namespace PEqualNP.Outside.L_meta_26033_aux
open Finset
def value {a : ℕ} (S : Finset (Fin a)) : ℕ := ∑ i ∈ S, 2^i.val

lemma value_eq {a} (S : Finset (Fin a)) :
    value S = ∑ i ∈ S.image Fin.val, 2^i := by
  rw [Finset.sum_image (fun _ _ _ _ h => Fin.ext h)]
  rfl

lemma value_bit {a} (S : Finset (Fin a)) (i : Fin a) :
    (value S).testBit i.val = true ↔ i ∈ S := by
  rw [← Nat.mem_bitIndices, ← List.mem_toFinset, value_eq, Finset.toFinset_bitIndices_sum_two_pow]
  simp [Fin.ext_iff.symm]

lemma value_bound {a} (S : Finset (Fin a)) : value S < 2^a := by
  have h : value S ≤ ∑ i ∈ Finset.range a, 2^i := by
    rw [value_eq]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro x hx
      obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_range.mpr y.isLt
    · intros; positivity
  have hs : ∑ i ∈ Finset.range a, 2^i = 2^a - 1 := by
    clear h S
    induction a with
    | zero => simp
    | succ a ih => rw [Finset.sum_range_succ, ih, pow_succ]; have := Nat.one_le_two_pow (n := a); omega
  rw [hs] at h
  have := Nat.one_le_two_pow (n := a)
  omega

def pack {a} (S : Finset (Fin a)) : Fin (2^a) := ⟨value S, value_bound S⟩

def bits {a} (x : Fin (2^a)) : Finset (Fin a) := univ.filter fun i => x.val.testBit i.val

@[simp] lemma bits_pack {a} (S : Finset (Fin a)) : bits (pack S) = S := by
  ext i
  simp [bits, pack, value_bit]

lemma bits_inj {a} : Function.Injective (@bits a) := by
  intro x y h
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < a
  · have e := Finset.ext_iff.mp h (⟨i,hi⟩ : Fin a)
    simpa [bits] using e
  · have hpow : 2^a ≤ 2^i := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le x.isLt hpow),
        Nat.testBit_lt_two_pow (lt_of_lt_of_le y.isLt hpow)]

@[simp] lemma pack_bits {a} (x : Fin (2^a)) : pack (bits x) = x := bits_inj (bits_pack _)

lemma pack_union {a} {A B : Finset (Fin a)} (h : Disjoint A B) :
    pack (A ∪ B) = pack A + pack B := by
  apply Fin.ext
  change value (A ∪ B) = (value A + value B) % 2^a
  have he : value (A ∪ B) = value A + value B := Finset.sum_union h
  rw [← he, Nat.mod_eq_of_lt (value_bound _)]

def coins {a} (J : Finset (Fin a)) := (univ : Finset (Fin (2^a))).filter fun s =>
  ∀ h : Fin a, s.val.testBit h.val = true → h ∈ J

def marked {a} (J : Finset (Fin a)) := (univ : Finset (Fin (2^a))).filter fun s =>
  ∀ h ∈ J, s.val.testBit h.val = false

lemma mem_coins {a} {J : Finset (Fin a)} {s} : s ∈ coins J ↔ bits s ⊆ J := by
  simp [coins, bits, Finset.subset_iff]

lemma mem_marked {a} {J : Finset (Fin a)} {s} : s ∈ marked J ↔ bits s ⊆ Jᶜ := by
  simp [marked, bits, Finset.subset_iff]
  grind

lemma coins_image {a} (J : Finset (Fin a)) : coins J = J.powerset.image pack := by
  ext s
  rw [mem_coins, Finset.mem_image]
  constructor
  · intro h; exact ⟨bits s, Finset.mem_powerset.mpr h, pack_bits s⟩
  · rintro ⟨S,hS,rfl⟩; simpa using Finset.mem_powerset.mp hS

lemma coins_card {a} (J : Finset (Fin a)) : (coins J).card = 2^J.card := by
  rw [coins_image, Finset.card_image_of_injective _ (Function.LeftInverse.injective bits_pack), Finset.card_powerset]

lemma marked_eq {a} (J : Finset (Fin a)) : marked J = coins Jᶜ := by
  ext; rw [mem_marked, mem_coins]

lemma mass {a} (J : Finset (Fin a)) : (coins J).card * (marked J).card = 2^a := by
  rw [marked_eq, coins_card, coins_card, ← pow_add]
  congr 1
  simp


def diff {a} (J : Finset (Fin a)) (z : ↥(marked J) × ↥(coins J)) : Fin (2^a) :=
  z.1.val - z.2.val

lemma diff_bij {a} (J : Finset (Fin a)) : Function.Bijective (diff J) := by
  classical
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨?_, by simpa [mul_comm] using mass J⟩
  rintro ⟨⟨m,hm⟩,⟨c,hc⟩⟩ ⟨⟨n,hn⟩,⟨d,hd⟩⟩ h
  change m-c=n-d at h
  have e : m+d = n+c := sub_eq_sub_iff_add_eq_add.mp h
  have M := mem_marked.mp hm
  have N := mem_marked.mp hn
  have C := mem_coins.mp hc
  have D := mem_coins.mp hd
  have hd₁ : Disjoint (bits m) (bits d) := Finset.disjoint_left.mpr (by
    intro i hi hi'; exact Finset.mem_compl.mp (M hi) (D hi'))
  have hd₂ : Disjoint (bits n) (bits c) := Finset.disjoint_left.mpr (by
    intro i hi hi'; exact Finset.mem_compl.mp (N hi) (C hi'))
  have he : bits m ∪ bits d = bits n ∪ bits c := by
    apply (Function.LeftInverse.injective bits_pack)
    simpa [pack_union hd₁, pack_union hd₂] using e
  have mn : bits m = bits n := by
    ext i
    have H := Finset.ext_iff.mp he i
    simp only [Finset.mem_union] at H
    by_cases hi : i ∈ J
    · have h1 : i ∉ bits m := fun h => Finset.mem_compl.mp (M h) hi
      have h2 : i ∉ bits n := fun h => Finset.mem_compl.mp (N h) hi
      simp [h1,h2]
    · exact (by simpa [show i ∉ bits d from fun hd => hi (D hd),
                         show i ∉ bits c from fun hc => hi (C hc)] using H)
  have hmn := bits_inj mn
  subst n
  have hdc := add_left_cancel e
  subst d
  rfl

lemma unique_coin {a} (J : Finset (Fin a)) (j : Fin (2^a)) :
    ∃! s : ↥(coins J), j+s.val ∈ marked J := by
  classical
  obtain ⟨⟨m,c⟩,h⟩ := (diff_bij J).2 j
  change m.val - c.val = j at h
  have hm : j+c.val=m.val := (eq_sub_iff_add_eq.mp h.symm)
  refine ⟨c, (show j+c.val ∈ marked J by rw [hm]; exact m.property), ?_⟩
  intro d hd
  have he : diff J (⟨j+d.val,hd⟩,d) = diff J (m,c) := by
    change j+d.val-d.val=m.val-c.val
    simp [h]
  exact congrArg Prod.snd ((diff_bij J).1 he)


lemma capture_sum {a} (J D : Finset (Fin (2^a))) (s : Fin (2^a)) :
    ((D.image (fun j => j+s)) ∩ J).card = ∑ j ∈ D, if j+s ∈ J then 1 else 0 := by
  classical
  have he : (D.image (fun j => j+s)) ∩ J = (D.filter (fun j => j+s ∈ J)).image (fun j => j+s) := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_image, Finset.mem_filter]
    grind
  rw [he, Finset.card_image_of_injective _ (add_left_injective s)]
  simp [Finset.sum_boole]

lemma fair_capture {a} (J : Finset (Fin a)) (D : Finset (Fin (2^a))) :
    ∑ s ∈ coins J, ((D.image (fun j => j+s)) ∩ marked J).card = D.card := by
  classical
  simp_rw [capture_sum]
  rw [Finset.sum_comm]
  have one (j : Fin (2^a)) : (∑ s ∈ coins J, if j+s ∈ marked J then 1 else 0 : ℕ) = 1 := by
    obtain ⟨c,hc,hu⟩ := unique_coin J j
    rw [Finset.sum_eq_single c.val]
    · simp [hc]
    · intro b hb hbc
      have h : j+b ∉ marked J := fun he => hbc (congrArg Subtype.val (hu ⟨b,hb⟩ he))
      simp [h]
    · simp [c.property]
  simp [one]

lemma fair_loss {a} (J : Finset (Fin a)) (D : Finset (Fin (2^a))) (N E L : ℕ)
    (hE : E = L*(marked J).card) (loss : Fin (2^a) → ℕ)
    (h : ∀ s, loss s + 2*L*((D.image (fun j => j+s)) ∩ marked J).card = N*D.card+E) :
    2^a*(∑ s ∈ coins J, loss s) + 2^J.card*2*D.card*E = 2^J.card*2^a*(N*D.card+E) := by
  classical
  have sumh := Finset.sum_congr (s₁ := coins J) rfl (fun s _ => h s)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, fair_capture, Finset.sum_const,
    nsmul_eq_mul, coins_card] at sumh
  have hmass := mass J
  rw [coins_card] at hmass
  calc
    _ = 2^a*((∑ s ∈ coins J, loss s) + 2*L*D.card) := by rw [hE]; linear_combination (2*L*D.card)*hmass
    _ = _ := by rw [sumh]; simp; ring

lemma scale {a k : ℕ} (ha : 6 ≤ a) (hk : 2*2^a ≤ k) (J : Finset (Fin a)) :
    let L := 2^k / (128*2^a)
    0 < L ∧ 2^J.card*(L*(marked J).card) = 2^k/128 := by
  dsimp only
  have hpow : a+7 ≤ 2*2^a := by
    clear hk J
    induction a, ha using Nat.le_induction with
    | base => decide
    | succ a ha ih => rw [pow_succ]; have := Nat.one_le_two_pow (n := a); omega
  have hex : k = (k-(7+a))+(7+a) := by omega
  have fac : 2^k = 2^(k-(7+a))*(128*2^a) := by
    conv_lhs => rw [hex, pow_add, pow_add]
    rfl
  have hpos : 0 < 128*2^a := by positivity
  have hL : 2^k / (128*2^a) = 2^(k-(7+a)) := by rw [fac, Nat.mul_div_cancel _ hpos]
  rw [hL]
  refine ⟨by positivity, ?_⟩
  have hmass := mass J
  rw [coins_card] at hmass
  calc
    _ = 2^(k-(7+a)) * (2^J.card * (marked J).card) := by ring
    _ = _ := by rw [hmass]; conv_rhs => rw [fac, show 2^(k-(7+a))*(128*2^a) = (2^(k-(7+a))*2^a)*128 by ring, Nat.mul_div_cancel _ (by decide)]

end PEqualNP.Outside.L_meta_26033_aux

namespace PEqualNP.Outside.L_meta_26033_aux
open Finset
private def lab {r} (j : Fin r) : ℕ := 2^(r+j.val)
private lemma lab_inj {r} : Function.Injective (@lab r) := by
  intro x y e
  have eq : r+x.val=r+y.val := Nat.pow_right_injective (by decide : 2 ≤ 2) e
  exact Fin.ext (by omega)

private def pair {r k : ℕ} (hk : 2*r ≤ k) (z : Fin (2^k) × Fin r) : Fin (2^k) × Fin (2^k) :=
  (z.1,⟨z.1.val ^^^ lab z.2, Nat.xor_lt_two_pow z.1.isLt (by apply Nat.pow_lt_pow_right (by decide); have := z.2.isLt; omega)⟩)

private lemma cancelxor (x y : ℕ) : x ^^^ (x ^^^ y) = y := by rw [← Nat.xor_assoc]; simp
private lemma pair_inj {r k} (hk : 2*r ≤ k) : Function.Injective (pair hk) := by
  rintro ⟨x,j⟩ ⟨y,l⟩ h
  have hxy : x=y := congrArg Prod.fst h
  subst y
  have hh := congrArg (fun z : Fin (2^k) × Fin (2^k) => x.val ^^^ z.2.val) h
  change x.val ^^^ (x.val ^^^ lab j) = x.val ^^^ (x.val ^^^ lab l) at hh
  simp only [cancelxor] at hh
  exact Prod.ext rfl (lab_inj hh)

private lemma pair_mem {r k} (hk : 2*r ≤ k) (D : Finset (Fin r)) (z : Fin (2^k) × Fin (2^k)) :
    z ∈ ((univ ×ˢ D).image (pair hk)) ↔ Nat.xor z.1.val z.2.val ∈ D.image lab := by
  constructor
  · rintro hz
    obtain ⟨⟨x,j⟩,h,rfl⟩ := mem_image.mp hz
    exact mem_image.mpr ⟨j,(mem_product.mp h).2,(cancelxor _ _).symm⟩
  · intro hz
    obtain ⟨j,hj,h⟩ := mem_image.mp hz
    refine mem_image.mpr ⟨(z.1,j),mem_product.mpr ⟨mem_univ _,hj⟩,Prod.ext rfl (Fin.ext ?_)⟩
    change z.1.val ^^^ lab j = z.2.val
    rw [h]; exact cancelxor _ _

private lemma loss_card {α : Type} [Fintype α] [DecidableEq α] (F : α → Bool) (A B : Finset α) :
    (univ.filter (fun z => xor (F z) (decide (z ∈ A)) ≠ xor (F z) (decide (z ∈ B)))).card
      + 2*(A ∩ B).card = B.card+A.card := by
  classical
  have he : univ.filter (fun z => xor (F z) (decide (z ∈ A)) ≠ xor (F z) (decide (z ∈ B))) =
      (A \ B) ∪ (B \ A) := by
    ext z
    by_cases hA : z ∈ A <;> by_cases hB : z ∈ B <;> cases F z <;> simp [hA,hB]
  rw [he, Finset.card_union_of_disjoint (by apply disjoint_left.mpr; simp; tauto)]
  have h1 := card_sdiff_add_card_inter A B
  have h2 := card_sdiff_add_card_inter B A
  rw [inter_comm B A] at h2
  omega

def precap {a} (M : Finset (Fin (2^a))) (s : Fin (2^a)) :=
  univ.filter fun j => j+s ∈ M

lemma precap_image {a} (M D : Finset (Fin (2^a))) (s : Fin (2^a)) :
    ((precap M s ∩ D).image (·+s)) = D.image (·+s) ∩ M := by
  ext j
  simp [precap]
  grind

lemma precap_card {a} (M : Finset (Fin (2^a))) (s : Fin (2^a)) : (precap M s).card = M.card := by
  have h := precap_image M univ s
  have hu : (univ : Finset (Fin (2^a))).image (·+s) = univ :=
    Finset.image_univ_of_surjective (Equiv.addRight s).surjective
  rw [hu,Finset.univ_inter,Finset.inter_univ] at h
  simpa only [Finset.card_image_of_injective _ (add_left_injective s)] using congrArg Finset.card h

lemma marked_cells {a k} (hk : 2*(2^a) ≤ k) (M : Finset (Fin (2^a))) (s : Fin (2^a))
    (L : ℕ) (hL : L ≤ 2^k) :
    ∃ A : Finset (Fin (2^k) × Fin (2^k)), A.card = L*M.card ∧
      ∀ D : Finset (Fin (2^a)), ∀ F : Fin (2^k) × Fin (2^k) → Bool,
      (univ.filter (fun z => xor (F z) (decide (z ∈ A)) ≠ xor (F z)
        (decide (Nat.xor z.1.val z.2.val ∈ D.image lab)))).card +
        2*L*((D.image (·+s)) ∩ M).card = 2^k*D.card+L*M.card := by
  classical
  obtain ⟨X,_,hX⟩ := Finset.exists_subset_card_eq (s := (univ : Finset (Fin (2^k)))) (n := L) (by simpa using hL)
  let A := (X ×ˢ precap M s).image (pair hk)
  have hA : A.card=L*M.card := by simp [A,Finset.card_image_of_injective _ (pair_inj hk),hX,precap_card]
  refine ⟨A,hA,?_⟩
  intro D F
  let B := ((univ ×ˢ D).image (pair hk))
  have hB : B.card=2^k*D.card := by simp [B,Finset.card_image_of_injective _ (pair_inj hk)]
  have inter : (A ∩ B).card=L*((D.image (·+s)) ∩ M).card := by
    change (((X ×ˢ precap M s).image (pair hk)) ∩ ((univ ×ˢ D).image (pair hk))).card=_
    rw [← Finset.image_inter _ _ (pair_inj hk),Finset.product_inter_product,
      Finset.card_image_of_injective _ (pair_inj hk),Finset.inter_univ,Finset.card_product,hX,
      ← precap_image, Finset.card_image_of_injective _ (add_left_injective s)]
  have h := loss_card F A B
  rw [inter,hA,hB,← mul_assoc] at h
  simpa only [B,pair_mem] using h

end PEqualNP.Outside.L_meta_26033_aux

open Finset
namespace PEqualNP.Outside.L_meta_26033_aux

lemma flat {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (f : G → ℝ) (hf : ∑ x, f x = 0)
    (t : ℕ) (ht : 0 < t) (ht' : t < Fintype.card G)
    (h : ∀ D : Finset G, D.card = t → 0 ≤ ∑ j ∈ D, f j) :
    ∀ x y, f x = f y := by
  classical
  have hzero (D : Finset G) (hD : D.card = t) : ∑ j ∈ D, f j = 0 := by
    have pos (s : G) : 0 ≤ ∑ j ∈ D, f (j+s) := by
      have e := h (D.image (·+s)) (by rwa [Finset.card_image_of_injective _ (add_left_injective s)])
      rwa [Finset.sum_image (fun _ _ _ _ => add_right_cancel)] at e
    have sum : ∑ s : G, ∑ j ∈ D, f (j+s) = 0 := by
      rw [sum_comm]
      exact sum_eq_zero fun j _ => by
        simpa using Equiv.sum_comp (Equiv.addLeft j) f |>.trans hf
    simpa using (Finset.sum_eq_zero_iff_of_nonneg (fun s _ => pos s)).mp sum 0 (mem_univ _)
  intro x y
  by_cases hxy : x=y
  · simp [hxy]
  have hcard : t-1 ≤ (((univ : Finset G).erase x).erase y).card := by
    rw [card_erase_of_mem (by simp [Ne.symm hxy]), card_erase_of_mem (mem_univ _), card_univ]
    omega
  obtain ⟨S,hS,hs⟩ := Finset.exists_subset_card_eq hcard
  have hx : x ∉ S := by intro he; simpa using hS he
  have hy : y ∉ S := by intro he; simpa using hS he
  have hxt := hzero (insert x S) (by rw [card_insert_of_notMem hx, hs]; omega)
  have hyt := hzero (insert y S) (by rw [card_insert_of_notMem hy, hs]; omega)
  rw [sum_insert hx] at hxt
  rw [sum_insert hy] at hyt
  linarith

lemma flat_zero {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (f : G → ℝ) (hf : ∑ x, f x = 0)
    (t : ℕ) (ht : 0 < t) (ht' : t < Fintype.card G)
    (h : ∀ D : Finset G, D.card = t → 0 ≤ ∑ j ∈ D, f j) :
    ∀ x, f x = 0 := by
  intro x
  have he := Finset.sum_congr (s₁ := (univ : Finset G)) rfl (fun y _ => flat f hf t ht ht' h y x)
  rw [hf, sum_const, card_univ, nsmul_eq_mul] at he
  exact (mul_eq_zero.mp he.symm).resolve_left (by exact_mod_cast Fintype.card_ne_zero)

end PEqualNP.Outside.L_meta_26033_aux

namespace PEqualNP.Outside.L_meta_26033_aux
open Finset
lemma lower_bound {a} (J : Finset (Fin a)) (N L : ℕ) (hL : 0 < L)
    (loss : Fin (2^a) → Finset (Fin (2^a)) → ℕ)
    (hloss : ∀ s D, loss s D + 2*L*((D.image (·+s)) ∩ marked J).card = N*D.card+L*(marked J).card)
    (t : ℕ) (ht : 0<t) (ht' : t<2^a) (p : Fin (2^a) → ℝ) (hp : ∀ s, 0 ≤ p s) (hp1 : ∑ s, p s=1)
    (h : ∀ D : Finset (Fin (2^a)), D.card=t →
      (2^a : ℝ)*(∑ s, p s*(loss s D : ℝ)) + 2*(t : ℝ)*(L*(marked J).card : ℕ) ≤
        (2^a : ℝ)*((N*t+L*(marked J).card : ℕ) : ℝ)) :
    2^J.card ≤ (univ.filter (fun s => 0 < p s)).card := by
  classical
  let M := marked J
  let r : ℝ := 2^a
  let score (j : Fin (2^a)) := ∑ s, if j+s ∈ M then p s else 0
  have hscore : ∑ j, score j = (M.card : ℝ) := by
    unfold score
    rw [sum_comm]
    have one (s : Fin (2^a)) : ∑ j, (if j+s ∈ M then p s else 0) = (M.card : ℝ)*p s := by
      rw [← Finset.sum_filter]
      simp [← precap_card M s, ← show (univ.filter (fun j => j+s ∈ M)) = precap M s from rfl, nsmul_eq_mul]
    simp_rw [one]
    rw [← Finset.mul_sum,hp1,mul_one]
  let f := fun j => r*score j-M.card
  have hf : ∑ j, f j=0 := by simp [f,Finset.sum_sub_distrib,← Finset.mul_sum,hscore,r]
  have hd (D : Finset (Fin (2^a))) (hD : D.card=t) : 0 ≤ ∑ j ∈ D, f j := by
    have e (s : Fin (2^a)) : (loss s D : ℝ) + (2*(L:ℝ))*∑ j ∈ D, (if j+s ∈ M then (1:ℝ) else 0) =
        (N*t+L*M.card : ℕ) := by
      have eq := hloss s D
      rw [capture_sum,hD] at eq
      exact_mod_cast eq
    have weigh := Finset.sum_congr (s₁ := (univ : Finset (Fin (2^a)))) rfl (fun s _ => congrArg (p s * ·) (e s))
    simp_rw [mul_add] at weigh
    rw [sum_add_distrib,← Finset.sum_mul,hp1,one_mul] at weigh
    have cap : (∑ s, p s * (2*(L:ℝ)*∑ j ∈ D, if j+s ∈ M then (1:ℝ) else 0)) =
        2*(L:ℝ)*∑ j ∈ D, score j := by
      simp only [score,Finset.mul_sum, mul_ite,mul_one,mul_zero]
      rw [sum_comm]
      apply sum_congr rfl
      intro j _
      apply sum_congr rfl
      intro s _
      split_ifs <;> ring
    rw [cap] at weigh
    have hi := h D hD
    change r*_+_ ≤ r*_ at hi
    rw [show ∑ j ∈ D, f j = r*(∑ j ∈ D, score j) - t*M.card by simp [f,sum_sub_distrib,← Finset.mul_sum,hD,nsmul_eq_mul]]
    change r*_+2*(t:ℝ)*((L*M.card : ℕ):ℝ) ≤ r*_ at hi
    push_cast at hi weigh
    have hc : 0 < (2:ℝ)*L := by positivity
    apply nonneg_of_mul_nonneg_right (a := 2*(L:ℝ)) _ hc
    nlinarith only [hi, congrArg (r * ·) weigh]
  have hz := flat_zero f hf t ht (by simpa using ht') hd
  have hM : 0 < M.card := by
    have hm := mass J
    change (coins J).card*M.card = 2^a at hm
    by_contra! e
    simp [Nat.eq_zero_of_le_zero e] at hm
    exact (Nat.ne_of_gt (Nat.two_pow_pos _)) hm.symm
  obtain ⟨m,hm⟩ := Finset.card_pos.mp hM
  have hcap (s : Fin (2^a)) : r*p s ≤ M.card := by
    have hsingle : p s ≤ score (m-s) := by
      unfold score
      simpa [hm] using (Finset.single_le_sum (s := (univ : Finset (Fin (2^a))))
        (f := fun z => if m-s+z ∈ M then p z else 0) (fun i _ => by split_ifs <;> simp [hp]) (Finset.mem_univ s))
    have eq := hz (m-s)
    change r*score (m-s)-M.card=0 at eq
    have hr : 0 ≤ r := by dsimp [r]; positivity
    linarith [mul_le_mul_of_nonneg_left hsingle hr]
  let S := univ.filter fun s => 0 < p s
  have hs : ∑ s ∈ S, p s=1 := by
    rw [← hp1]
    apply sum_subset (Finset.filter_subset _ _)
    intro s hs hns
    have : ¬ 0 < p s := fun h => hns (Finset.mem_filter.mpr ⟨hs,h⟩)
    linarith [hp s]
  have H := sum_le_sum (s := S) (fun s _ => hcap s)
  rw [← Finset.mul_sum, hs,mul_one,sum_const,nsmul_eq_mul] at H
  have hm := mass J
  rw [coins_card] at hm
  have he : (2^J.card:ℝ)*M.card=r := by dsimp [M,r]; exact_mod_cast hm
  rw [← he] at H
  exact_mod_cast (le_of_mul_le_mul_right H (by exact_mod_cast hM : (0:ℝ)<M.card))

end PEqualNP.Outside.L_meta_26033_aux


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
namespace PEqualNP.Outside.L_meta_26033_aux

private def step (n : ℕ) (C : Circuit) (g : Gate) : Circuit :=
  ⟨C.gates ++ [g], n+C.gates.length⟩

private lemma wlength (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length+C.gates.length := by
  rcases C with ⟨gs,out⟩
  induction gs using List.reverseRecOn with
  | nil => simp [Circuit.wires]
  | append_singleton gs g ih => simp [Circuit.wires, List.foldl_append] at ih ⊢; omega

private lemma wires_step (n) (C : Circuit) (g : Gate) (x : List Bool) :
    (step n C g).wires x = C.wires x ++ [g.op.eval (g.inputs.map fun i => (C.wires x).getD i false)] := by
  simp [step,Circuit.wires,List.foldl_append]

private lemma look_old (C : Circuit) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (C.wires x).getD i false = x.getD i false := by
  rcases C with ⟨gs,out⟩
  induction gs using List.reverseRecOn with
  | nil => rfl
  | append_singleton gs g ih =>
    change ((step x.length ⟨gs,out⟩ g).wires x).getD i false = _
    rw [wires_step, List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [wlength]; omega), ← List.getD_eq_getElem?_getD, ih]

private lemma step_eval (n) (C : Circuit) (g : Gate) (x : List Bool) (hx : x.length=n) :
    (step n C g).eval x = g.op.eval (g.inputs.map fun i => (C.wires x).getD i false) := by
  simp [Circuit.eval,step, Circuit.wires,List.foldl_append, List.getD_eq_getElem?_getD,
    ← show (C.wires x).length=n+C.gates.length by rw [wlength,hx]]
    
private def cell {n m} (toggle : Bool) (C : Circuit) (z : Fin n × Fin m) : Circuit :=
  let C₁ := step (n+m) C ⟨if toggle then .not else .or,[C.output]⟩
  let C₂ := step (n+m) C₁ ⟨.and,[z.1.val,n+z.2.val]⟩
  step (n+m) C₂ ⟨if toggle then .mod 2 else .or,[C₁.output,C₂.output]⟩

private lemma old_step (n) (C : Circuit) (g : Gate) (x : List Bool) (i : ℕ)
    (hi : i < x.length+C.gates.length) :
    ((step n C g).wires x).getD i false = (C.wires x).getD i false := by
  rw [wires_step, List.getD_eq_getElem?_getD, List.getElem?_append_left (by rwa [wlength]), ← List.getD_eq_getElem?_getD]

private lemma left_input {n m} (u : Fin n) (v : Fin m) (i : Fin n) :
    (oneEach u v).getD i.val false = decide (u=i) := by
  simp [oneEach,List.getD_eq_getElem?_getD,List.getElem?_append_left,i.isLt,eq_comm]
private lemma right_input {n m} (u : Fin n) (v : Fin m) (i : Fin m) :
    (oneEach u v).getD (n+i.val) false = decide (v=i) := by
  simp [oneEach,List.getD_eq_getElem?_getD,eq_comm]

private lemma cell_eval {n m} (b) (C : Circuit) (z : Fin n × Fin m) (u : Fin n) (v : Fin m) :
    (cell b C z).eval (oneEach u v) =
      if b then xor (C.eval (oneEach u v)) (decide ((u,v)=z))
      else C.eval (oneEach u v) || decide ((u,v)=z) := by
  let x := oneEach u v
  have hx : x.length=n+m := by simp [x,oneEach]
  let g : Gate := ⟨if b then .not else .or,[C.output]⟩
  let A := step (n+m) C g
  let d : Gate := ⟨.and,[z.1.val,n+z.2.val]⟩
  let B := step (n+m) A d
  have hA : A.eval x = (if b then !(C.eval x) else C.eval x) := by
    rw [show A = step (n+m) C g by rfl, step_eval _ _ _ _ hx]
    cases b <;> simp [g,GateOp.eval,Circuit.eval]
  have hB : B.eval x = decide ((u,v)=z) := by
    rw [show B = step (n+m) A d by rfl, step_eval _ _ _ _ hx]
    simp only [d,List.map_cons,List.map_nil,GateOp.eval,List.all_cons,List.all_nil,id_eq,Bool.and_true]
    rw [look_old A x _ (by rw [hx]; have := z.1.isLt; omega),
      look_old A x _ (by rw [hx]; have := z.2.isLt; omega),left_input,right_input]
    simp [Prod.ext_iff]
  have hold : (B.wires x).getD A.output false = A.eval x := by
    apply old_step
    simp [A,step,hx]
  change (step (n+m) B ⟨_,[A.output,B.output]⟩).eval x = _
  rw [step_eval _ _ _ _ hx]
  simp only [List.map_cons, List.map_nil, hold, ← show B.eval x = (B.wires x).getD B.output false by rfl,hA,hB]
  change _ = if b then xor (C.eval x) (decide ((u,v)=z)) else C.eval x || decide ((u,v)=z)
  cases b <;> cases C.eval x <;> cases decide ((u,v)=z) <;> decide


private def fan (C : Circuit) := ∀ g ∈ C.gates, g.inputs.length ≤ 2

private lemma cell_valid {n m} (b) (C : Circuit) (z : Fin n × Fin m) (hf : fan C)
    (hm : b=false → Monotone2 C) : fan (cell b C z) ∧ (b=false → Monotone2 (cell b C z)) := by
  constructor
  · intro g hg
    simp only [cell,step,List.mem_append,List.mem_singleton] at hg
    rcases hg with ((hg | rfl) | rfl) | rfl
    · exact hf _ hg
    all_goals simp
  · rintro rfl g hg
    simp only [cell,step,List.mem_append,List.mem_singleton] at hg
    rcases hg with ((hg | rfl) | rfl) | rfl
    · exact hm rfl _ hg
    all_goals simp

private lemma extend {n m} (b : Bool) (C : Circuit) (hf : fan C) (hm : b=false → Monotone2 C)
    (S : Finset (Fin n × Fin m)) :
    ∃ K : Circuit, fan K ∧ (b=false → Monotone2 K) ∧ K.size ≤ C.size+3*S.card ∧
      ∀ u v, K.eval (oneEach u v) =
        if b then xor (C.eval (oneEach u v)) (decide ((u,v) ∈ S))
        else C.eval (oneEach u v) || decide ((u,v) ∈ S) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨C,hf,hm,by simp,by intro u v; cases b <;> simp⟩
  | @insert z S hz ih =>
    obtain ⟨K,hK,hM,hlen,hev⟩ := ih
    obtain ⟨hf',hm'⟩ := cell_valid b K z hK hM
    refine ⟨cell b K z,hf',hm',?_,?_⟩
    · have eq : (cell b K z).size = K.size+3 := by simp [cell,step,Circuit.size]
      rw [eq,Finset.card_insert_of_notMem hz]; omega
    · intro u v
      rw [cell_eval,hev]
      by_cases he : (u,v)=z
      · subst z; cases b <;> simp [hz]
      · cases b <;> simp [he]

private lemma sparse {n m} (S : Finset (Fin n × Fin m)) :
    RepSizeAtMost (fun u v => decide ((u,v) ∈ S)) (1+3*S.card) := by
  let C : Circuit := ⟨[⟨.or,[]⟩], n+m⟩
  have hm : Monotone2 C := by intro g hg; simp [C] at hg; subst g; simp
  obtain ⟨K,_,hmono,hs,he⟩ := extend false C (fun g hg => (hm g hg).2) (fun _ => hm) S
  refine ⟨K,hmono rfl,hs,?_⟩
  intro u v
  have hfalse : C.eval (oneEach u v)=false := by
    simp [C,Circuit.eval,Circuit.wires,GateOp.eval,List.getD_eq_getElem?_getD,
      ← show (oneEach u v).length = n+m by simp [oneEach]]
  simpa [hfalse] using he u v

lemma sel {a k : ℕ} (hk : 2*2^a ≤ k) :
    let r := 2^a
    let N := 2^k
    ∃ C : Circuit, fan C ∧ C.size ≤ 2*N+1+3*(2^r*r) ∧
      ∀ (u v : Fin N), C.eval (oneEach u v) = u.val.testBit (v.val % r) := by
  classical
  intro r N
  have hr : 0 < r := by positivity
  have hrk : r ≤ k := by dsimp [r]; omega
  have hn : 2^r ≤ N := Nat.pow_le_pow_right (by decide) hrk
  have hrn : r ≤ N := le_trans (Nat.le_of_lt (Nat.lt_two_pow_self)) hn
  let row : Fin N → Fin (2^r) := fun x => ⟨x.val % 2^r, Nat.mod_lt _ (by positivity)⟩
  let col : Fin N → Fin r := fun x => ⟨x.val % r,Nat.mod_lt _ hr⟩
  have hrow : Function.Surjective row := fun x => ⟨⟨x.val,lt_of_lt_of_le x.isLt hn⟩,Fin.ext (Nat.mod_eq_of_lt x.isLt)⟩
  have hcol : Function.Surjective col := fun x => ⟨⟨x.val,lt_of_lt_of_le x.isLt hrn⟩,Fin.ext (Nat.mod_eq_of_lt x.isLt)⟩
  let S := (Finset.univ : Finset (Fin (2^r) × Fin r)).filter fun z => z.1.val.testBit z.2.val
  let Q := fun (x : Fin (2^r)) (y : Fin r) => decide ((x,y) ∈ S)
  have hcard : S.card ≤ 2^r*r := by simpa using Finset.card_le_univ S
  obtain ⟨C,hm,hs,he⟩ := Compression.compress N N (2^r) r (1+3*S.card) Q row col hrow hcol (sparse S)
  refine ⟨C,fun g hg => (hm g hg).2,hs.trans ?_,?_⟩
  · have h1 := Nat.sub_le N (2^r); have h2 := Nat.sub_le N r; omega
  · intro u v
    rw [he u v]
    simp [Q,S,row,col,Nat.testBit_mod_two_pow,Nat.mod_lt _ hr]

lemma budget_aux (r : ℕ) (hr : 64 ≤ r) :
    64*(1+3*(2^r*r)) ≤ 2^(2*r) := by
  induction r, hr using Nat.le_induction with
  | base => decide
  | succ r hr ih =>
    rw [show 2*(r+1)=2*r+2 by omega,pow_add 2 (2*r) 2,pow_succ 2 r]
    have hp : (2^r : ℕ) ≤ 2^r*r := Nat.le_mul_of_pos_right _ (by omega)
    change 64*(1+3*(2^r*2*(r+1))) ≤ 2^(2*r)*4
    nlinarith

end PEqualNP.Outside.L_meta_26033_aux

open PEqualNP.Outside.L_meta_26033_aux

theorem PEqualNP.Outside.L_meta_26033 : (∀ (a k : ℕ), 6 ≤ a → 2*2^a ≤ k → ∀ J : Finset (Fin a),
  let r := 2^a
  let N := 2^k
  let I := Fin r
  let X := Fin N
  let q := 2^J.card
  let L := N/(128*r)
  let marked := (Finset.univ : Finset I).filter (fun j => ∀ h ∈ J, j.val.testBit h.val = false)
  let coins := (Finset.univ : Finset I).filter (fun s =>
    ∀ h : Fin a, s.val.testBit h.val = true → h ∈ J)
  let label := fun j : I => 2^(r+j.val)
  let loss := fun (C : PEqualNP.CircuitLowerBounds.Circuit) (D : Finset I) =>
    ((Finset.univ : Finset (X × X)).filter (fun z =>
      C.eval (PEqualNP.Represents.oneEach z.1 z.2) ≠
        xor (z.1.val.testBit (z.2.val % r)) (decide (Nat.xor z.1.val z.2.val ∈ D.image label)))).card
  let E := L*marked.card
  ∃ rot : I → PEqualNP.CircuitLowerBounds.Circuit,
    (∀ s, (∀ g ∈ (rot s).gates, g.inputs.length ≤ 2) ∧
      16*((rot s).gates.countP (fun g => g.inputs.length == 2)) ≤ 33*N ∧
      ∀ D : Finset I, loss (rot s) D + 2*L*((D.image (fun j => j+s)) ∩ marked).card = N*D.card+E) ∧
    coins.card = q ∧ q*E = N/128 ∧
    (∀ D : Finset I, r*(∑ s ∈ coins, loss (rot s) D) + q*2*D.card*E = q*r*(N*D.card+E)) ∧
    ∀ t : ℕ, 0 < t → t < r → ∀ p : I → ℝ, (∀ s, 0 ≤ p s) → (∑ s, p s) = 1 →
      (∀ D : Finset I, D.card = t →
        (r : ℝ)*(∑ s : I, p s * (loss (rot s) D : ℝ)) + 2*(t : ℝ)*(E : ℝ) ≤
          (r : ℝ)*((N*t+E : ℕ) : ℝ)) →
      q ≤ ((Finset.univ : Finset I).filter (fun s => 0 < p s)).card) := by
  classical
  intro a k ha hk J r N I X q L mset cset label loss E
  have hsc := scale ha hk J
  change 0 < L ∧ q*(L*(marked J).card) = N/128 at hsc
  have hm : mset = marked J := rfl
  have hcoins : cset = coins J := rfl
  have hr : 64 ≤ r := by change 2^6 ≤ 2^a; exact Nat.pow_le_pow_right (by decide) ha
  obtain ⟨baseC,hfan,hbase,heval⟩ := sel hk
  have hnum : 64*(1+3*(2^r*r)) ≤ N := (budget_aux r hr).trans (Nat.pow_le_pow_right (by decide) hk)
  have hmark : 128*(L*mset.card) ≤ N := by
    have hmr : mset.card ≤ r := by simpa [I] using Finset.card_le_univ mset
    calc
      _ ≤ 128*(L*r) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hmr)
      _ = L*(128*r) := by ring
      _ ≤ N := Nat.div_mul_le_self _ _
  have one (s : I) : ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      fan C ∧ 16*(C.gates.countP (fun g => g.inputs.length == 2)) ≤ 33*N ∧
      ∀ D : Finset I, loss C D + 2*L*((D.image (fun j => j+s)) ∩ mset).card = N*D.card+E := by
    obtain ⟨A,hA,hl⟩ := marked_cells hk mset s L (Nat.div_le_self ..)
    obtain ⟨C,hf,_,hs,hC⟩ := extend true baseC hfan (by simp) A
    refine ⟨C,hf,?_,?_⟩
    · have hc : C.gates.countP (fun g => g.inputs.length == 2) ≤ C.size := List.countP_le_length
      change baseC.size ≤ 2*N+1+3*(2^r*r) at hbase
      rw [hA] at hs
      omega
    · intro D
      let F := fun z : X × X => z.1.val.testBit (z.2.val % r)
      have ev (z : X × X) : C.eval (PEqualNP.Represents.oneEach z.1 z.2) = xor (F z) (decide (z ∈ A)) := by
        simpa [heval,F] using hC z.1 z.2
      dsimp only [loss]
      simp_rw [ev]
      exact hl D F
  choose rot hfan' hsize hlos using one
  refine ⟨rot,fun s => ⟨hfan' s,hsize s,hlos s⟩,coins_card J,hsc.2,?_,?_⟩
  · intro D
    exact fair_loss J D N E L rfl (fun s => loss (rot s) D) (fun s => hlos s D)
  · intro t ht htr p hp hp1 hb
    apply lower_bound J N L hsc.1 (fun s D => loss (rot s) D) hlos t ht htr p hp hp1
    intro D hD
    have hh := hb D hD
    have cast_r : (r : ℝ) = 2^a := by simp [r]
    rw [cast_r] at hh
    exact hh
