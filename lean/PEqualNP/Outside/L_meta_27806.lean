import Mathlib
import PEqualNP.Defs

-- Replacing the NOT of a row-column OR by AND/OR gates on the one-hot promise, reusing k mixed input ORs.
--
-- The circuit is OR(x_u, y_v), NOT of it, then AND/OR gates only. The new circuit starts with the old first
-- gate and the k mixed ORs OR(x_{x h}, y_{y h}), ORs those into Q, ORs the row inputs other than u and the
-- x h into L, the column inputs other than v and the y h into R, and puts Q OR (L AND R) in place of the NOT.
-- That is 1 + k + (k-1) + (n-2-k) + (m-2-k) + 2 = n+m-2 gates. The old gates after the NOT are then copied
-- with their wire numbers translated, except that every copy of a mixed OR is dropped and read from the
-- front instead; at least k gates are dropped. On a promise input the new signal equals the old one unless
-- the old one is false and the new one true, which happens only at (u, y h) or (x h, v), where the old
-- output is true; AND/OR gates can only keep it true. Size: (n+m-2) + (size-2-k).

namespace PEqualNP.Outside.L_meta_27806

open PEqualNP.CircuitLowerBounds

/-- The wire list after running a gate list on a wire list: the fold inside `Circuit.wires`. -/
def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem run_nil (w : List Bool) : run [] w = w := rfl

theorem run_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    run (g :: gs) w = run gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

theorem run_append (gs hs : List Gate) (w : List Bool) : run (gs ++ hs) w = run hs (run gs w) := by
  simp [run, List.foldl_append]

theorem run_len (gs : List Gate) : ∀ w : List Bool, (run gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [run]
  | cons g gs ih => intro w; rw [run_cons, ih]; simp; omega

theorem run_old (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (run gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    rw [run_cons, ih _ i (by simp; omega)]
    exact List.getD_append _ _ _ _ hi

theorem eval_eq (gs : List Gate) (out : ℕ) (w : List Bool) :
    Circuit.eval ⟨gs, out⟩ w = (run gs w).getD out false := rfl

theorem getD_last (V : List Bool) (e : Bool) : (V ++ [e]).getD V.length false = e := by simp

theorem getD_two_old (V : List Bool) (a b : Bool) (i : ℕ) (hi : i < V.length) :
    (V ++ [a] ++ [b]).getD i false = V.getD i false := by
  rw [List.getD_append _ _ _ _ (by simp; omega), List.getD_append _ _ _ _ hi]

theorem getD_two_first (V : List Bool) (a b : Bool) : (V ++ [a] ++ [b]).getD V.length false = a := by
  rw [List.getD_append _ _ _ _ (by simp), getD_last]

theorem getD_two_last (V : List Bool) (a b : Bool) : (V ++ [a] ++ [b]).getD (V.length + 1) false = b := by
  have h : (V ++ [a]).length = V.length + 1 := by simp
  rw [← h, getD_last]

/-- Gates reading only the first wires: their values are added in one go. -/
theorem run_flat (gs : List Gate) : ∀ (ws ext : List Bool),
    (∀ g ∈ gs, ∀ a ∈ g.inputs, a < ws.length) →
    run gs (ws ++ ext) =
      ws ++ ext ++ gs.map (fun g => g.op.eval (g.inputs.map fun i => ws.getD i false)) := by
  induction gs with
  | nil => intro ws ext _; simp [run]
  | cons g gs ih =>
    intro ws ext h
    have e : (g.inputs.map fun i => (ws ++ ext).getD i false) = g.inputs.map fun i => ws.getD i false :=
      List.map_congr_left (fun a ha => List.getD_append _ _ _ _ (h g (by simp) a ha))
    rw [run_cons, e, List.append_assoc, ih ws _ (fun g' hg' => h g' (by simp [hg']))]
    simp

theorem or_two (f : ℕ → Bool) (a b : ℕ) : GateOp.or.eval ([a, b].map f) = (f a || f b) := by
  simp [GateOp.eval]

/-- The gate is an AND or an OR of at most two wires. -/
def Ok (g : Gate) : Prop := (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

/-- The new value is at least the old one, and equal to it when `e` holds. -/
def Rel (e : Prop) (a b : Bool) : Prop := (a = true → b = true) ∧ (e → a = b)

theorem rel_refl (e : Prop) (a : Bool) : Rel e a a := ⟨id, fun _ => rfl⟩

theorem rel_eval (e : Prop) (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l : List ℕ) (f f' : ℕ → Bool) (ψ : ℕ → ℕ) (h : ∀ a ∈ l, Rel e (f a) (f' (ψ a))) :
    Rel e (op.eval (l.map f)) (op.eval ((l.map ψ).map f')) := by
  constructor
  · rcases hop with rfl | rfl
    · simp only [GateOp.eval, List.all_eq_true, List.mem_map, id]
      rintro hall b ⟨c, ⟨a, ha, rfl⟩, rfl⟩
      exact (h a ha).1 (hall _ ⟨a, ha, rfl⟩)
    · simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
      rintro ⟨b, ⟨a, ha, rfl⟩, hb⟩
      exact ⟨_, ⟨_, ⟨a, ha, rfl⟩, rfl⟩, (h a ha).1 hb⟩
  · intro he
    have e1 : l.map f = (l.map ψ).map f' := by
      rw [List.map_map]
      exact List.map_congr_left (fun a ha => (h a ha).2 he)
    rw [e1]

theorem any_congr_on {l : List ℕ} {f g : ℕ → Bool} (h : ∀ c ∈ l, f c = g c) : l.any f = l.any g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.any_cons]
    rw [h a (by simp), ih (fun c hc => h c (by simp [hc]))]

/-- A chain of OR gates over wire `a` and the wires of `l`. -/
theorem stage_cons (l : List ℕ) : ∀ (base a : ℕ), a < base → (∀ b ∈ l, b < base) →
    ∃ (G : List Gate) (o : ℕ), G.length = l.length ∧ (∀ g ∈ G, Ok g) ∧ o < base + G.length ∧
      ∀ ws : List Bool, ws.length = base →
        (run G ws).getD o false = (ws.getD a false || l.any (fun b => ws.getD b false)) := by
  induction l with
  | nil =>
    intro base a ha _
    exact ⟨[], a, rfl, by simp, by simpa using ha, by intro ws _; simp [run]⟩
  | cons b l ih =>
    intro base a ha hl
    obtain ⟨G, o, hlen, hok, ho, hval⟩ := ih (base + 1) base (by omega)
      (fun c hc => by have := hl c (by simp [hc]); omega)
    refine ⟨⟨GateOp.or, [a, b]⟩ :: G, o, by simp [hlen], ?_, by simp; omega, ?_⟩
    · intro g hg
      rcases List.mem_cons.1 hg with rfl | hg
      · exact ⟨Or.inr rfl, by simp⟩
      · exact hok g hg
    · intro ws hws
      rw [run_cons, hval _ (by simp [hws])]
      have h1 : (ws ++ [GateOp.or.eval ([a, b].map fun i => ws.getD i false)]).getD base false
          = (ws.getD a false || ws.getD b false) := by
        rw [← hws, getD_last]; simp [GateOp.eval]
      have h2 : l.any (fun c => (ws ++ [GateOp.or.eval ([a, b].map fun i => ws.getD i false)]).getD c false)
          = l.any (fun c => ws.getD c false) :=
        any_congr_on (fun c hc => List.getD_append _ _ _ _ (by rw [hws]; exact hl c (by simp [hc])))
      rw [h1, h2]
      simp [Bool.or_assoc]

/-- A chain of OR gates over the wires of a nonempty list. -/
theorem stage (l : List ℕ) (hne : l ≠ []) (base : ℕ) (hl : ∀ b ∈ l, b < base) :
    ∃ (G : List Gate) (o : ℕ), G.length + 1 = l.length ∧ (∀ g ∈ G, Ok g) ∧ o < base + G.length ∧
      ∀ ws : List Bool, ws.length = base →
        (run G ws).getD o false = l.any (fun b => ws.getD b false) := by
  rcases l with _ | ⟨a, l⟩
  · exact absurd rfl hne
  obtain ⟨G, o, hlen, hok, ho, hval⟩ := stage_cons l base a (hl a (by simp))
    (fun b hb => hl b (by simp [hb]))
  exact ⟨G, o, by simp [hlen], hok, ho, by intro ws hws; rw [hval ws hws]; simp⟩

/-- The gate is one of the mixed ORs. -/
noncomputable def isDrop {k : ℕ} (xs ys : Fin k → ℕ) (g : Gate) : Bool :=
  @decide (∃ h, g.op = GateOp.or ∧ g.inputs = [xs h, ys h]) (Classical.propDecidable _)

theorem isDrop_iff {k : ℕ} (xs ys : Fin k → ℕ) (g : Gate) :
    isDrop xs ys g = true ↔ ∃ h, g.op = GateOp.or ∧ g.inputs = [xs h, ys h] := by
  simp [isDrop]

theorem count_drop {k : ℕ} (xs ys : Fin k → ℕ) (hinj : Function.Injective xs) (S : List Gate)
    (h : ∀ t : Fin k, ∃ g ∈ S, g.op = GateOp.or ∧ g.inputs = [xs t, ys t]) :
    k ≤ S.countP (isDrop xs ys) := by
  choose gate hmem hop hin using h
  have hinjg : Function.Injective gate := by
    intro a b hab
    have e := hin a
    rw [hab, hin b] at e
    simp only [List.cons.injEq, and_true] at e
    exact (hinj e.1).symm
  have hnd : (List.ofFn gate).Nodup := List.nodup_ofFn.2 hinjg
  have hsub : List.ofFn gate ⊆ S.filter (isDrop xs ys) := by
    intro g hg
    obtain ⟨t, rfl⟩ : ∃ t, gate t = g := by simpa [List.mem_ofFn] using hg
    exact List.mem_filter.2 ⟨hmem t, (isDrop_iff xs ys _).2 ⟨t, hop t, hin t⟩⟩
  have hle := (List.subperm_of_subset hnd hsub).length_le
  rw [List.countP_eq_length_filter]
  simpa using hle

/-- Copy the gates with translated wire numbers, dropping the mixed ORs. -/
theorem sim {k : ℕ} (xs ys d : Fin k → ℕ) :
    ∀ (S : List Gate) (L L' : ℕ) (φ : ℕ → ℕ),
      (∀ g ∈ S, Ok g) →
      (∀ j < S.length, ∀ a ∈ (S.getD j ⟨GateOp.or, []⟩).inputs, a < L + j) →
      (∀ i < L, φ i < L') →
      (∀ h, xs h < L ∧ ys h < L ∧ d h < L') →
      ∃ (S' : List Gate) (φ' : ℕ → ℕ),
        S'.length + S.countP (isDrop xs ys) = S.length ∧
        (∀ g ∈ S', Ok g) ∧
        (∀ i < L + S.length, φ' i < L' + S'.length) ∧
        ∀ (e : Prop) (ws ws' : List Bool), ws.length = L → ws'.length = L' →
          (∀ h, (ws.getD (xs h) false || ws.getD (ys h) false) = ws'.getD (d h) false) →
          (∀ i < L, Rel e (ws.getD i false) (ws'.getD (φ i) false)) →
          ∀ i < L + S.length, Rel e ((run S ws).getD i false) ((run S' ws').getD (φ' i) false) := by
  intro S
  induction S with
  | nil =>
    intro L L' φ _ _ hφ _
    refine ⟨[], φ, by simp, by simp, by simpa using hφ, ?_⟩
    intro e ws ws' _ _ _ hR i hi
    exact hR i (by simpa using hi)
  | cons g S ih =>
    intro L L' φ hok hrb hφ hd
    have hg : Ok g := hok g (by simp)
    have hgin : ∀ a ∈ g.inputs, a < L := by
      intro a ha
      have := hrb 0 (by simp) a (by simpa using ha)
      simpa using this
    have hrb' : ∀ j < S.length, ∀ a ∈ (S.getD j ⟨GateOp.or, []⟩).inputs, a < (L + 1) + j := by
      intro j hj a ha
      have := hrb (j + 1) (by simp; omega) a (by simpa using ha)
      omega
    have hok' : ∀ g' ∈ S, Ok g' := fun g' hg' => hok g' (by simp [hg'])
    by_cases hD : isDrop xs ys g = true
    · obtain ⟨h, hgop, hgi⟩ := (isDrop_iff xs ys g).1 hD
      obtain ⟨S', φ', hlen, hS', hφ', hsim⟩ := ih (L + 1) L' (Function.update φ L (d h)) hok' hrb'
        (by
          intro i hi
          by_cases hiL : i = L
          · rw [hiL, Function.update_self]; exact (hd h).2.2
          · rw [Function.update_of_ne hiL]; exact hφ i (by omega))
        (fun t => ⟨by have := (hd t).1; omega, by have := (hd t).2.1; omega, (hd t).2.2⟩)
      refine ⟨S', φ', ?_, hS', ?_, ?_⟩
      · simp [hD]; omega
      · intro i hi; exact hφ' i (by simp at hi; omega)
      · intro e ws ws' hws hws' hdrop hR i hi
        rw [run_cons]
        refine hsim e _ ws' (by simp [hws]) hws' ?_ ?_ i (by simp at hi; omega)
        · intro t
          rw [List.getD_append _ _ _ _ (by rw [hws]; exact (hd t).1),
            List.getD_append _ _ _ _ (by rw [hws]; exact (hd t).2.1)]
          exact hdrop t
        · intro i' hi'
          by_cases hiL : i' = L
          · rw [hiL, Function.update_self]
            have hv : (ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]).getD L false
                = ws'.getD (d h) false := by
              rw [← hws, getD_last, hgop, hgi, ← hdrop h]; simp [GateOp.eval]
            rw [hv]; exact rel_refl e _
          · rw [Function.update_of_ne hiL, List.getD_append _ _ _ _ (by omega)]
            exact hR i' (by omega)
    · obtain ⟨S', φ', hlen, hS', hφ', hsim⟩ := ih (L + 1) (L' + 1) (Function.update φ L L') hok' hrb'
        (by
          intro i hi
          by_cases hiL : i = L
          · rw [hiL, Function.update_self]; omega
          · rw [Function.update_of_ne hiL]; have := hφ i (by omega); omega)
        (fun t => ⟨by have := (hd t).1; omega, by have := (hd t).2.1; omega,
          by have := (hd t).2.2; omega⟩)
      refine ⟨⟨g.op, g.inputs.map φ⟩ :: S', φ', ?_, ?_, ?_, ?_⟩
      · simp [hD]; omega
      · intro g' hg'
        rcases List.mem_cons.1 hg' with rfl | hg'
        · exact ⟨hg.1, by simpa using hg.2⟩
        · exact hS' g' hg'
      · intro i hi; have := hφ' i (by simp at hi; omega); simp; omega
      · intro e ws ws' hws hws' hdrop hR i hi
        rw [run_cons, run_cons]
        refine hsim e _ _ (by simp [hws]) (by simp [hws']) ?_ ?_ i (by simp at hi; omega)
        · intro t
          rw [List.getD_append _ _ _ _ (by rw [hws]; exact (hd t).1),
            List.getD_append _ _ _ _ (by rw [hws]; exact (hd t).2.1),
            List.getD_append _ _ _ _ (by rw [hws']; exact (hd t).2.2)]
          exact hdrop t
        · intro i' hi'
          by_cases hiL : i' = L
          · rw [hiL, Function.update_self]
            have h1 : (ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]).getD L false
                = g.op.eval (g.inputs.map fun i => ws.getD i false) := by rw [← hws, getD_last]
            have h2 : (ws' ++ [g.op.eval ((g.inputs.map φ).map fun i => ws'.getD i false)]).getD L' false
                = g.op.eval ((g.inputs.map φ).map fun i => ws'.getD i false) := by
              rw [← hws', getD_last]
            rw [h1, h2]
            exact rel_eval e g.op hg.1 g.inputs _ _ φ (fun a ha => hR a (hgin a ha))
          · rw [Function.update_of_ne hiL, List.getD_append _ _ _ _ (by omega),
              List.getD_append _ _ _ _ (by have := hφ i' (by omega); omega)]
            exact hR i' (by omega)

open PEqualNP.Represents in
theorem one_len {n m : ℕ} (xi : Fin n) (yj : Fin m) : (oneEach xi yj).length = n + m := by
  simp [oneEach]

open PEqualNP.Represents in
theorem one_left {n m : ℕ} (xi : Fin n) (yj : Fin m) (i : Fin n) :
    (oneEach xi yj).getD i.val false = decide (i = xi) := by
  unfold oneEach
  rw [List.getD_append _ _ _ _ (by simp)]
  simp [List.getD_eq_getElem?_getD]

open PEqualNP.Represents in
theorem one_right {n m : ℕ} (xi : Fin n) (yj : Fin m) (j : Fin m) :
    (oneEach xi yj).getD (n + j.val) false = decide (j = yj) := by
  unfold oneEach
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp [List.getD_eq_getElem?_getD]

open PEqualNP.Represents in
/-- The new front: the old first gate, the mixed ORs, and the replacement of the NOT as its last gate. -/
theorem front (n m k : ℕ) (u : Fin n) (v : Fin m) (x : Fin k ↪ Fin n) (y : Fin k ↪ Fin m)
    (hk : 1 ≤ k) (hn : k + 2 ≤ n) (hm : k + 2 ≤ m) (hxu : ∀ h, x h ≠ u) (hyv : ∀ h, y h ≠ v) :
    ∃ P : List Gate, P.length = n + m - 2 ∧ (∀ g ∈ P, Ok g) ∧
      ∀ (xi : Fin n) (yj : Fin m),
        (run P (oneEach xi yj)).getD (n + m) false =
          ((oneEach xi yj).getD u.val false || (oneEach xi yj).getD (n + v.val) false) ∧
        (∀ h : Fin k, (run P (oneEach xi yj)).getD (n + m + 1 + h.val) false =
          ((oneEach xi yj).getD (x h).val false || (oneEach xi yj).getD (n + (y h).val) false)) ∧
        ((run P (oneEach xi yj)).getD (n + m + P.length - 1) false = true ↔
          ((∃ h, x h = xi ∨ y h = yj) ∨
            ((xi ≠ u ∧ ∀ h, x h ≠ xi) ∧ (yj ≠ v ∧ ∀ h, y h ≠ yj)))) := by
  obtain ⟨B, hB⟩ : ∃ B : List Gate, B = ⟨GateOp.or, [u.val, n + v.val]⟩ ::
      List.ofFn (fun h : Fin k => (⟨GateOp.or, [(x h).val, n + (y h).val]⟩ : Gate)) := ⟨_, rfl⟩
  have hBlen : B.length = k + 1 := by simp [hB]
  have hBok : ∀ g ∈ B, Ok g := by
    intro g hg
    rw [hB] at hg
    rcases List.mem_cons.1 hg with rfl | hg
    · exact ⟨Or.inr rfl, by simp⟩
    · obtain ⟨t, rfl⟩ : ∃ t, (⟨GateOp.or, [(x t).val, n + (y t).val]⟩ : Gate) = g := by
        simpa [List.mem_ofFn] using hg
      exact ⟨Or.inr rfl, by simp⟩
  have hBin : ∀ g ∈ B, ∀ a ∈ g.inputs, a < n + m := by
    intro g hg a ha
    rw [hB] at hg
    rcases List.mem_cons.1 hg with rfl | hg
    · have := u.isLt
      have := v.isLt
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl <;> omega
    · obtain ⟨t, rfl⟩ : ∃ t, (⟨GateOp.or, [(x t).val, n + (y t).val]⟩ : Gate) = g := by
        simpa [List.mem_ofFn] using hg
      have := (x t).isLt
      have := (y t).isLt
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl <;> omega
  -- the OR of the mixed ORs
  obtain ⟨gatesQ, oQ, hQlen, hQok, hoQ, hQ⟩ := stage (List.ofFn (fun h : Fin k => n + m + 1 + h.val))
    (by intro hc; have := congrArg List.length hc; simp at this; omega) (n + m + (k + 1))
    (by
      intro b hb
      obtain ⟨t, rfl⟩ : ∃ t : Fin k, n + m + 1 + t.val = b := by simpa [List.mem_ofFn] using hb
      have := t.isLt
      omega)
  simp only [List.length_ofFn] at hQlen
  -- the OR of the remaining row inputs
  obtain ⟨Ll, hLl⟩ : ∃ Ll : List ℕ, Ll =
      (((Finset.univ : Finset (Fin n)) \ insert u (Finset.univ.image x)).toList.map Fin.val) := ⟨_, rfl⟩
  have hLllen : Ll.length = n - (k + 1) := by
    rw [hLl, List.length_map, Finset.length_toList, Finset.card_univ_sdiff,
      Finset.card_insert_of_notMem (by simpa using hxu),
      Finset.card_image_of_injective _ x.injective]
    simp
  obtain ⟨gatesL, oL, hLlen, hLok, hoL, hL⟩ := stage Ll
    (by intro hc; rw [hc] at hLllen; simp at hLllen; omega) (n + m + (k + 1) + gatesQ.length)
    (by
      intro b hb
      rw [hLl] at hb
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hb
      have := i.isLt
      omega)
  -- the OR of the remaining column inputs
  obtain ⟨Rl, hRl⟩ : ∃ Rl : List ℕ, Rl =
      (((Finset.univ : Finset (Fin m)) \ insert v (Finset.univ.image y)).toList.map
        (fun j => n + j.val)) := ⟨_, rfl⟩
  have hRllen : Rl.length = m - (k + 1) := by
    rw [hRl, List.length_map, Finset.length_toList, Finset.card_univ_sdiff,
      Finset.card_insert_of_notMem (by simpa using hyv),
      Finset.card_image_of_injective _ y.injective]
    simp
  obtain ⟨gatesR, oR, hRlen, hRok, hoR, hR⟩ := stage Rl
    (by intro hc; rw [hc] at hRllen; simp at hRllen; omega)
    (n + m + (k + 1) + gatesQ.length + gatesL.length)
    (by
      intro b hb
      rw [hRl] at hb
      obtain ⟨j, -, rfl⟩ := List.mem_map.1 hb
      have := j.isLt
      omega)
  refine ⟨B ++ gatesQ ++ gatesL ++ gatesR ++ [Gate.mk GateOp.and [oL, oR],
    Gate.mk GateOp.or [oQ, n + m + (k + 1) + gatesQ.length + gatesL.length + gatesR.length]], ?_, ?_, ?_⟩
  · simp [hBlen]; omega
  · intro g hg
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with (((hg | hg) | hg) | hg) | (rfl | rfl)
    · exact hBok g hg
    · exact hQok g hg
    · exact hLok g hg
    · exact hRok g hg
    · exact ⟨Or.inl rfl, by simp⟩
    · exact ⟨Or.inr rfl, by simp⟩
  · intro xi yj
    have hidx : n + m + (B ++ gatesQ ++ gatesL ++ gatesR ++ [Gate.mk GateOp.and [oL, oR],
        Gate.mk GateOp.or [oQ, n + m + (k + 1) + gatesQ.length + gatesL.length + gatesR.length]]).length - 1
        = n + m + (k + 1) + gatesQ.length + gatesL.length + gatesR.length + 1 := by
      simp [hBlen]; omega
    rw [hidx]
    obtain ⟨inp, hinp⟩ : ∃ inp, inp = oneEach xi yj := ⟨_, rfl⟩
    rw [← hinp]
    have hil : inp.length = n + m := by rw [hinp]; exact one_len xi yj
    have hiL : ∀ i : Fin n, inp.getD i.val false = decide (i = xi) := by
      intro i; rw [hinp]; exact one_left xi yj i
    have hiR : ∀ j : Fin m, inp.getD (n + j.val) false = decide (j = yj) := by
      intro j; rw [hinp]; exact one_right xi yj j
    obtain ⟨w1, hw1⟩ : ∃ w1, w1 = run B inp := ⟨_, rfl⟩
    obtain ⟨w2, hw2⟩ : ∃ w2, w2 = run gatesQ w1 := ⟨_, rfl⟩
    obtain ⟨w3, hw3⟩ : ∃ w3, w3 = run gatesL w2 := ⟨_, rfl⟩
    obtain ⟨w4, hw4⟩ : ∃ w4, w4 = run gatesR w3 := ⟨_, rfl⟩
    have l1 : w1.length = n + m + (k + 1) := by rw [hw1, run_len, hil, hBlen]
    have l2 : w2.length = n + m + (k + 1) + gatesQ.length := by rw [hw2, run_len, l1]
    have l3 : w3.length = n + m + (k + 1) + gatesQ.length + gatesL.length := by rw [hw3, run_len, l2]
    have l4 : w4.length = n + m + (k + 1) + gatesQ.length + gatesL.length + gatesR.length := by
      rw [hw4, run_len, l3]
    have hw1' : w1 = inp ++ B.map (fun g => g.op.eval (g.inputs.map fun i => inp.getD i false)) := by
      have := run_flat B inp [] (by intro g hg a ha; rw [hil]; exact hBin g hg a ha)
      simpa [hw1] using this
    have v0 : w1.getD (n + m) false = (inp.getD u.val false || inp.getD (n + v.val) false) := by
      rw [hw1', List.getD_append_right _ _ _ _ (by omega), hil, hB]
      simp [GateOp.eval]
    have vh : ∀ h : Fin k, w1.getD (n + m + 1 + h.val) false =
        (inp.getD (x h).val false || inp.getD (n + (y h).val) false) := by
      intro h
      have e : n + m + 1 + h.val - (n + m) = h.val + 1 := by omega
      rw [hw1', List.getD_append_right _ _ _ _ (by omega), hil, e, hB]
      simp [GateOp.eval, List.getD_eq_getElem?_getD]
    have vin : ∀ i < n + m, w1.getD i false = inp.getD i false := by
      intro i hi; rw [hw1]; exact run_old B inp i (by omega)
    have t2 : ∀ i < n + m + (k + 1), w2.getD i false = w1.getD i false := by
      intro i hi; rw [hw2]; exact run_old gatesQ w1 i (by omega)
    have t3 : ∀ i < n + m + (k + 1) + gatesQ.length, w3.getD i false = w2.getD i false := by
      intro i hi; rw [hw3]; exact run_old gatesL w2 i (by omega)
    have t4 : ∀ i < n + m + (k + 1) + gatesQ.length + gatesL.length, w4.getD i false = w3.getD i false := by
      intro i hi; rw [hw4]; exact run_old gatesR w3 i (by omega)
    have vQ : w2.getD oQ false = true ↔ ∃ h, x h = xi ∨ y h = yj := by
      rw [hw2, hQ w1 l1, List.any_eq_true]
      constructor
      · rintro ⟨b, hb, hbv⟩
        obtain ⟨t, rfl⟩ : ∃ t : Fin k, n + m + 1 + t.val = b := by simpa [List.mem_ofFn] using hb
        rw [vh t, hiL, hiR] at hbv
        exact ⟨t, by simpa using hbv⟩
      · rintro ⟨t, ht⟩
        refine ⟨n + m + 1 + t.val, by simp [List.mem_ofFn], ?_⟩
        rw [vh t, hiL, hiR]
        simpa using ht
    have vL : w3.getD oL false = true ↔ (xi ≠ u ∧ ∀ h, x h ≠ xi) := by
      rw [hw3, hL w2 l2, List.any_eq_true]
      constructor
      · rintro ⟨b, hb, hbv⟩
        rw [hLl] at hb
        obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hb
        have := i.isLt
        rw [t2 _ (by omega), vin _ (by omega), hiL] at hbv
        have hix : i = xi := by simpa using hbv
        subst hix
        simpa using hi
      · rintro ⟨h1, h2⟩
        have := xi.isLt
        refine ⟨xi.val, ?_, ?_⟩
        · rw [hLl]
          exact List.mem_map.2 ⟨xi, by simpa using And.intro h1 h2, rfl⟩
        · rw [t2 _ (by omega), vin _ (by omega), hiL]; simp
    have vR : w4.getD oR false = true ↔ (yj ≠ v ∧ ∀ h, y h ≠ yj) := by
      rw [hw4, hR w3 l3, List.any_eq_true]
      constructor
      · rintro ⟨b, hb, hbv⟩
        rw [hRl] at hb
        obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hb
        have := j.isLt
        rw [t3 _ (by omega), t2 _ (by omega), vin _ (by omega), hiR] at hbv
        have hjy : j = yj := by simpa using hbv
        subst hjy
        simpa using hj
      · rintro ⟨h1, h2⟩
        have := yj.isLt
        refine ⟨n + yj.val, ?_, ?_⟩
        · rw [hRl]
          exact List.mem_map.2 ⟨yj, by simpa using And.intro h1 h2, rfl⟩
        · rw [t3 _ (by omega), t2 _ (by omega), vin _ (by omega), hiR]; simp
    have hrun : run (B ++ gatesQ ++ gatesL ++ gatesR ++ [Gate.mk GateOp.and [oL, oR],
        Gate.mk GateOp.or [oQ, n + m + (k + 1) + gatesQ.length + gatesL.length + gatesR.length]]) inp
        = w4 ++ [w4.getD oL false && w4.getD oR false]
          ++ [w4.getD oQ false || (w4.getD oL false && w4.getD oR false)] := by
      rw [run_append, run_append, run_append, run_append, ← hw1, ← hw2, ← hw3, ← hw4,
        run_cons, run_cons, run_nil]
      have eA : GateOp.and.eval ([oL, oR].map fun i => w4.getD i false)
          = (w4.getD oL false && w4.getD oR false) := by simp [GateOp.eval]
      rw [eA]
      have eO : GateOp.or.eval ([oQ, n + m + (k + 1) + gatesQ.length + gatesL.length + gatesR.length].map
          fun i => (w4 ++ [w4.getD oL false && w4.getD oR false]).getD i false)
          = (w4.getD oQ false || (w4.getD oL false && w4.getD oR false)) := by
        have a1 : (w4 ++ [w4.getD oL false && w4.getD oR false]).getD oQ false = w4.getD oQ false :=
          List.getD_append _ _ _ _ (by omega)
        have a2 : (w4 ++ [w4.getD oL false && w4.getD oR false]).getD
            (n + m + (k + 1) + gatesQ.length + gatesL.length + gatesR.length) false
            = (w4.getD oL false && w4.getD oR false) := by rw [← l4, getD_last]
        rw [or_two, a1, a2]
      rw [eO]
    rw [hrun]
    refine ⟨?_, ?_, ?_⟩
    · rw [getD_two_old _ _ _ _ (by omega), t4 _ (by omega), t3 _ (by omega), t2 _ (by omega), v0]
    · intro h
      have := h.isLt
      rw [getD_two_old _ _ _ _ (by omega), t4 _ (by omega), t3 _ (by omega), t2 _ (by omega), vh h]
    · rw [← l4, getD_two_last, Bool.or_eq_true, Bool.and_eq_true, t4 oQ (by omega), t3 oQ (by omega),
        t4 oL (by omega), vQ, vL, vR]

open PEqualNP.Represents in
theorem main (n m k : ℕ) (A : Fin n → Fin m → Bool) (u : Fin n) (v : Fin m)
    (x : Fin k ↪ Fin n) (y : Fin k ↪ Fin m) (C : Circuit)
    (hk : 1 ≤ k) (hn : k + 2 ≤ n) (hm : k + 2 ≤ m)
    (hF : PEqualNP.MetaComplexity.FanInTwo C)
    (hRB : PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C)
    (hRep : Represents A C)
    (h0 : C.gates[0]? = some ⟨GateOp.or, [u.val, n + v.val]⟩)
    (h1 : C.gates[1]? = some ⟨GateOp.not, [n + m]⟩)
    (hsuf : ∀ g ∈ C.gates.drop 2, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hh : ∀ h, x h ≠ u ∧ y h ≠ v ∧ A (x h) v = true ∧ A u (y h) = true ∧
      ∃ g ∈ C.gates.drop 2, g.op = GateOp.or ∧ g.inputs = [(x h).val, n + (y h).val]) :
    RepSizeAtMost A (C.size + (n + m - (4 + k))) := by
  obtain ⟨gates, out⟩ := C
  rcases gates with _ | ⟨g0, _ | ⟨g1, S⟩⟩
  · simp at h0
  · simp at h1
  simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at h0 h1
  subst h0
  subst h1
  simp only [List.drop_succ_cons, List.drop_zero] at hsuf hh
  obtain ⟨P, hPlen, hPok, hPsem⟩ := front n m k u v x y hk hn hm (fun h => (hh h).1)
    (fun h => (hh h).2.1)
  have hSok : ∀ g ∈ S, Ok g := fun g hg => ⟨hsuf g hg, (hF g (by simp [hg])).2⟩
  have hSrb : ∀ j < S.length, ∀ a ∈ (S.getD j ⟨GateOp.or, []⟩).inputs, a < (n + m + 2) + j := by
    intro j hj a ha
    have := hRB (j + 2) (by simp; omega) a
      (by simpa [PEqualNP.MetaComplexity.NestedCover.gateAt] using ha)
    omega
  obtain ⟨S', φ', hlen, hS'ok, hφ', hsim⟩ := sim (fun h : Fin k => (x h).val)
    (fun h : Fin k => n + (y h).val) (fun h : Fin k => n + m + 1 + h.val) S (n + m + 2)
    (n + m + P.length) (fun i => if i = n + m + 1 then n + m + P.length - 1 else i) hSok hSrb
    (by intro i hi; split_ifs <;> omega)
    (by
      intro h
      have := (x h).isLt
      have := (y h).isLt
      have := h.isLt
      refine ⟨by omega, by omega, by omega⟩)
  have hcount : k ≤ S.countP (isDrop (fun h : Fin k => (x h).val) (fun h : Fin k => n + (y h).val)) :=
    count_drop _ _ (Fin.val_injective.comp x.injective) S (fun t => (hh t).2.2.2.2)
  have hout : out < n + m + 2 + S.length := by
    by_contra hcon
    have e := hRep (x ⟨0, hk⟩) v
    rw [(hh ⟨0, hk⟩).2.2.1, eval_eq, List.getD_eq_default _ _ (by
      rw [run_len, one_len]; simp; omega)] at e
    exact Bool.false_ne_true e
  refine ⟨⟨P ++ S', φ' out⟩, ?_, ?_, ?_⟩
  · intro g hg
    have hg' : Ok g := by
      rcases List.mem_append.1 hg with hg | hg
      · exact hPok g hg
      · exact hS'ok g hg
    exact ⟨by simpa using hg'.1, hg'.2⟩
  · show (P ++ S').length ≤ (_ :: _ :: S).length + (n + m - (4 + k))
    simp only [List.length_append, List.length_cons]
    omega
  · intro xi yj
    obtain ⟨hp0, hph, hpO⟩ := hPsem xi yj
    have hA := hRep xi yj
    rw [eval_eq, run_cons, run_cons] at hA
    rw [eval_eq, run_append]
    have hiL := one_left xi yj
    have hiR := one_right xi yj
    have hil := one_len xi yj
    generalize oneEach xi yj = inp at hp0 hph hpO hA hiL hiR hil ⊢
    obtain ⟨a0, ha0⟩ : ∃ a0, a0 = (inp.getD u.val false || inp.getD (n + v.val) false) := ⟨_, rfl⟩
    have e1 : GateOp.or.eval ([u.val, n + v.val].map fun i => inp.getD i false) = a0 := by
      simp [GateOp.eval, ha0]
    rw [e1] at hA
    have e2 : GateOp.not.eval ([n + m].map fun i => (inp ++ [a0]).getD i false) = !a0 := by
      have e3 : (inp ++ [a0]).getD (n + m) false = a0 := by rw [← hil, getD_last]
      rw [show GateOp.not.eval ([n + m].map fun i => (inp ++ [a0]).getD i false)
        = !((inp ++ [a0]).getD (n + m) false) from rfl, e3]
    rw [e2] at hA
    obtain ⟨vO, hvO⟩ : ∃ vO, vO = (run P inp).getD (n + m + P.length - 1) false := ⟨_, rfl⟩
    rw [← hvO] at hpO
    have ha0' : a0 = true ↔ (u = xi ∨ v = yj) := by
      rw [ha0, hiL, hiR]; simp
    have hmono : (!a0) = true → vO = true := by
      intro hna
      have hna' : ¬ (u = xi ∨ v = yj) := by
        intro hc
        rw [ha0'.2 hc] at hna
        exact Bool.false_ne_true hna
      rw [hpO]
      by_cases hq : ∃ h, x h = xi ∨ y h = yj
      · exact Or.inl hq
      · refine Or.inr ⟨⟨fun hc => hna' (Or.inl hc.symm), fun h hc => hq ⟨h, Or.inl hc⟩⟩,
          ⟨fun hc => hna' (Or.inr hc.symm), fun h hc => hq ⟨h, Or.inr hc⟩⟩⟩
    have hrel := hsim ((!a0) = vO) (inp ++ [a0] ++ [!a0]) (run P inp)
      (by simp [hil]) (by rw [run_len, hil])
      (by
        intro h
        have := (x h).isLt
        have := (y h).isLt
        rw [getD_two_old _ _ _ _ (by omega), getD_two_old _ _ _ _ (by omega)]
        exact (hph h).symm)
      (by
        intro i hi
        by_cases hi1 : i = n + m + 1
        · rw [ite_eq_left_of_eq_true _ _ (eq_true hi1), hi1, ← hvO]
          have e4 : (inp ++ [a0] ++ [!a0]).getD (n + m + 1) false = !a0 := by
            rw [← hil, getD_two_last]
          rw [e4]
          exact ⟨hmono, id⟩
        · rw [ite_eq_right_of_eq_false _ _ (eq_false hi1)]
          by_cases hi0 : i = n + m
          · have e5 : (inp ++ [a0] ++ [!a0]).getD (n + m) false = a0 := by
              rw [← hil, getD_two_first]
            rw [hi0, e5, hp0, ← ha0]
            exact rel_refl _ _
          · rw [getD_two_old _ _ _ _ (by omega), run_old P inp i (by omega)]
            exact rel_refl _ _)
      out hout
    rw [hA] at hrel
    by_cases he : (!a0) = vO
    · exact (hrel.2 he).symm
    · have hat : a0 = true ∧ vO = true := by
        revert he hmono
        cases a0 <;> cases vO <;> simp
      have hAt : A xi yj = true := by
        rcases ha0'.1 hat.1 with hux | hvy
        · subst hux
          rcases hpO.1 hat.2 with ⟨h, hx | hy⟩ | hc
          · exact absurd hx (hh h).1
          · rw [← hy]; exact (hh h).2.2.2.1
          · exact absurd rfl hc.1.1
        · subst hvy
          rcases hpO.1 hat.2 with ⟨h, hx | hy⟩ | hc
          · rw [← hx]; exact (hh h).2.2.1
          · exact absurd hy (hh h).2.1
          · exact absurd rfl hc.2.1
      rw [hAt, hrel.1 hAt]

end PEqualNP.Outside.L_meta_27806

theorem PEqualNP.Outside.L_meta_27806 : ∀ (n m k : Nat) (A : Fin n → Fin m → Bool) (u : Fin n) (v : Fin m)
    (x : Fin k ↪ Fin n) (y : Fin k ↪ Fin m) (C : PEqualNP.CircuitLowerBounds.Circuit),
  1 ≤ k → k+2 ≤ n → k+2 ≤ m →
  PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+m) C →
  PEqualNP.Represents.Represents A C →
  C.gates[0]? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [u.val,n+v.val]⟩ →
  C.gates[1]? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [n+m]⟩ →
  (∀ g ∈ C.gates.drop 2, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) →
  (∀ h, x h ≠ u ∧ y h ≠ v ∧ A (x h) v = true ∧ A u (y h) = true ∧
    ∃ g ∈ C.gates.drop 2, g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ g.inputs = [(x h).val,n+(y h).val]) →
  PEqualNP.Represents.RepSizeAtMost A (C.size + (n+m-(4+k))) := by
  intro n m k A u v x y C hk hn hm hF hRB hRep h0 h1 hsuf hh
  exact PEqualNP.Outside.L_meta_27806.main n m k A u v x y C hk hn hm hF hRB hRep h0 h1 hsuf hh
