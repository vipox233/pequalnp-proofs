import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1185

open PEqualNP.CircuitLowerBounds

def stepO (ov : ℕ → Option Bool) (w : List Bool) (g : Gate) : List Bool :=
  w ++ [match ov w.length with
    | some v => v
    | none => g.op.eval (g.inputs.map fun i => w.getD i false)]

def wO (ov : ℕ → Option Bool) (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (stepO ov) x

def isNotOp : GateOp → Bool
  | GateOp.not => true
  | _ => false

def actN (ov : ℕ → Option Bool) (n : ℕ) (gs : List Gate) : ℕ :=
  ((Finset.range gs.length).filter
    (fun j => isNotOp (gs.getD j ⟨GateOp.or, []⟩).op = true ∧ (ov (n + j)).isNone = true)).card

theorem wO_snoc (ov : ℕ → Option Bool) (gs : List Gate) (g : Gate) (x : List Bool) :
    wO ov (gs ++ [g]) x = stepO ov (wO ov gs x) g := by
  simp [wO, List.foldl_append]

theorem wO_len (ov : ℕ → Option Bool) (gs : List Gate) (x : List Bool) :
    (wO ov gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [wO]
  | append_singleton gs g ih => rw [wO_snoc]; simp [stepO, ih]; omega

theorem foldl_ext (ov : ℕ → Option Bool) (hs : List Gate) :
    ∀ w : List Bool, ∃ t, hs.foldl (stepO ov) w = w ++ t := by
  induction hs with
  | nil => intro w; exact ⟨[], by simp⟩
  | cons g hs ih =>
    intro w
    obtain ⟨t, ht⟩ := ih (stepO ov w g)
    exact ⟨_, by rw [List.foldl_cons, ht, stepO, List.append_assoc]⟩

theorem wO_prefix (ov : ℕ → Option Bool) (gs hs : List Gate) (x : List Bool) (i : ℕ)
    (hi : i < x.length + gs.length) :
    (wO ov (gs ++ hs) x).getD i false = (wO ov gs x).getD i false := by
  obtain ⟨t, ht⟩ := foldl_ext ov hs (wO ov gs x)
  have : wO ov (gs ++ hs) x = wO ov gs x ++ t := by
    rw [wO, List.foldl_append]; exact ht
  rw [this, List.getD_append _ _ _ _ (by rw [wO_len]; exact hi)]

theorem wO_last (ov : ℕ → Option Bool) (gs : List Gate) (g : Gate) (x : List Bool) :
    (wO ov (gs ++ [g]) x).getD (x.length + gs.length) false =
      (match ov (x.length + gs.length) with
        | some v => v
        | none => g.op.eval (g.inputs.map fun i => (wO ov gs x).getD i false)) := by
  rw [wO_snoc, stepO, List.getD_append_right _ _ _ _ (by rw [wO_len])]
  simp [wO_len]

def LeW (x y : List Bool) : Prop := ∀ i, x.getD i false = true → y.getD i false = true

theorem all_mono (l : List ℕ) (f g : ℕ → Bool) (h : ∀ i, f i = true → g i = true) :
    (l.map f).all id = true → (l.map g).all id = true := by
  simp only [List.all_map, List.all_eq_true, Function.comp, id]
  intro hh i hi; exact h i (hh i hi)

theorem any_mono (l : List ℕ) (f g : ℕ → Bool) (h : ∀ i, f i = true → g i = true) :
    (l.map f).any id = true → (l.map g).any id = true := by
  simp only [List.any_map, List.any_eq_true, Function.comp, id]
  rintro ⟨i, hi, hf⟩; exact ⟨i, hi, h i hf⟩

theorem mono_wO (ov : ℕ → Option Bool) (n : ℕ) (gs : List Gate)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (hna : actN ov n gs = 0) (x y : List Bool) (hx : x.length = n) (hy : y.length = n)
    (hxy : LeW x y) : LeW (wO ov gs x) (wO ov gs y) := by
  induction gs using List.reverseRecOn with
  | nil => simpa [wO] using hxy
  | append_singleton gs g ih =>
    have hg' : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not :=
      fun g' h' => hg g' (List.mem_append_left _ h')
    have hlast : ¬ (isNotOp g.op = true ∧ (ov (n + gs.length)).isNone = true) := by
      intro hc
      have : gs.length ∈ (Finset.range (gs ++ [g]).length).filter
          (fun j => isNotOp ((gs ++ [g]).getD j ⟨GateOp.or, []⟩).op = true ∧
            (ov (n + j)).isNone = true) := by
        simp only [Finset.mem_filter, Finset.mem_range, List.length_append, List.length_singleton]
        refine ⟨by omega, ?_⟩
        rw [List.getD_append_right _ _ _ _ le_rfl]; simpa using hc
      unfold actN at hna
      rw [Finset.card_eq_zero] at hna
      rw [hna] at this; simp at this
    have hna' : actN ov n gs = 0 := by
      unfold actN at hna ⊢
      rw [Finset.card_eq_zero] at hna ⊢
      rw [Finset.eq_empty_iff_forall_notMem] at hna ⊢
      intro j hj
      apply hna j
      simp only [Finset.mem_filter, Finset.mem_range, List.length_append,
        List.length_singleton] at hj ⊢
      refine ⟨by omega, ?_⟩
      rw [List.getD_append _ _ _ _ hj.1]; exact hj.2
    have IH := ih hg' hna'
    intro i hi
    have hlx := wO_len ov gs x
    have hly := wO_len ov gs y
    rw [wO_snoc, stepO] at hi ⊢
    by_cases hlt : i < n + gs.length
    · rw [List.getD_append _ _ _ _ (by omega)] at hi ⊢
      exact IH i hi
    · by_cases heq : i = n + gs.length
      · subst heq
        rw [List.getD_append_right _ _ _ _ (by omega)] at hi ⊢
        rw [hlx, hx] at hi; rw [hly, hy]
        simp only [Nat.sub_self, List.getD_cons_zero] at hi ⊢
        revert hi
        cases hov : ov (n + gs.length) with
        | some v => simp
        | none =>
          simp only
          rcases hg g (List.mem_append_right _ (List.mem_singleton_self g)) with h | h | h
          · rw [h]; exact all_mono _ _ _ (fun j hj => IH j hj)
          · rw [h]; exact any_mono _ _ _ (fun j hj => IH j hj)
          · exact absurd ⟨by rw [h]; rfl, by rw [hov]; rfl⟩ hlast
      · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
        simp at hi

theorem agree (ov : ℕ → Option Bool) (gs : List Gate) (x : List Bool) (q : ℕ) (v : Bool)
    (hq : ov q = none) (hv : (wO ov gs x).getD q false = v) :
    wO (Function.update ov q (some v)) gs x = wO ov gs x := by
  have key : ∀ k ≤ gs.length, wO (Function.update ov q (some v)) (gs.take k) x =
      wO ov (gs.take k) x := by
    intro k
    induction k with
    | zero => intro _; simp [wO]
    | succ k ih =>
      intro hk
      have htake : gs.take (k + 1) = gs.take k ++ [gs[k]'(by omega)] := by
        rw [List.take_add_one, List.getElem?_eq_getElem (by omega)]; rfl
      rw [htake, wO_snoc, wO_snoc, ih (by omega)]
      unfold stepO
      congr 2
      have hlen : (wO ov (gs.take k) x).length = x.length + k := by
        rw [wO_len]; simp; omega
      rw [hlen]
      by_cases hqk : x.length + k = q
      · have hq' : ov (x.length + k) = none := by rw [hqk]; exact hq
        rw [show Function.update ov q (some v) (x.length + k) = some v by
          rw [hqk, Function.update_self], hq']
        simp only
        rw [← hv, ← hqk]
        have hsplit : gs = gs.take (k + 1) ++ gs.drop (k + 1) := (List.take_append_drop _ _).symm
        have e1 := wO_prefix ov (gs.take (k + 1)) (gs.drop (k + 1)) x (x.length + k)
          (by simp; omega)
        rw [← hsplit] at e1
        rw [e1, htake]
        have := wO_last ov (gs.take k) (gs[k]'(by omega)) x
        have hl : (gs.take k).length = k := by simp; omega
        rw [hl, hq'] at this
        rw [this]
      · rw [Function.update_of_ne hqk]
  have := key gs.length le_rfl
  rwa [List.take_length] at this

theorem actN_update (ov : ℕ → Option Bool) (n : ℕ) (gs : List Gate) (p : ℕ)
    (hp : p ∈ (Finset.range gs.length).filter
      (fun j => isNotOp (gs.getD j ⟨GateOp.or, []⟩).op = true ∧ (ov (n + j)).isNone = true))
    (v : Bool) : actN (Function.update ov (n + p) (some v)) n gs + 1 ≤ actN ov n gs := by
  unfold actN
  have hsub : (Finset.range gs.length).filter
      (fun j => isNotOp (gs.getD j ⟨GateOp.or, []⟩).op = true ∧
        ((Function.update ov (n + p) (some v)) (n + j)).isNone = true) ⊆
      ((Finset.range gs.length).filter
      (fun j => isNotOp (gs.getD j ⟨GateOp.or, []⟩).op = true ∧ (ov (n + j)).isNone = true)).erase p := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_erase] at hj ⊢
    by_cases hjp : j = p
    · subst hjp; simp at hj
    · rw [Function.update_of_ne (by omega)] at hj
      exact ⟨hjp, hj⟩
  have := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem hp] at this
  have : 0 < ((Finset.range gs.length).filter
      (fun j => isNotOp (gs.getD j ⟨GateOp.or, []⟩).op = true ∧ (ov (n + j)).isNone = true)).card :=
    Finset.card_pos.mpr ⟨p, hp⟩
  omega

def Dec (ov : ℕ → Option Bool) (gs : List Gate) (X : ℕ → List Bool) (k : ℕ) : Prop :=
  ∃ i, (wO ov gs (X k)).getD i false = true ∧ (wO ov gs (X (k + 1))).getD i false = false

theorem isNotOp_eq {o : GateOp} (h : isNotOp o = true) : o = GateOp.not := by
  cases o <;> simp_all [isNotOp]

theorem markov (n : ℕ) (gs : List Gate)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (X : ℕ → List Bool) (hlen : ∀ k, (X k).length = n)
    (hX : ∀ k l, k ≤ l → LeW (X k) (X l)) :
    ∀ r : ℕ, ∀ ov : ℕ → Option Bool, actN ov n gs ≤ r →
      ∀ K : Finset ℕ, (∀ k ∈ K, Dec ov gs X k) → K.card + 1 ≤ 2 ^ r := by
  classical
  intro r
  induction r with
  | zero =>
    intro ov hov K hK
    have h0 : actN ov n gs = 0 := by omega
    rcases K.eq_empty_or_nonempty with he | ⟨k, hk⟩
    · simp [he]
    · obtain ⟨i, h1, h2⟩ := hK k hk
      have := mono_wO ov n gs hg h0 _ _ (hlen k) (hlen (k + 1)) (hX k (k + 1) (by omega)) i h1
      rw [h2] at this; exact absurd this (by simp)
  | succ r ih =>
    intro ov hov K hK
    by_cases h0 : actN ov n gs = 0
    · rcases K.eq_empty_or_nonempty with he | ⟨k, hk⟩
      · simp [he]; exact Nat.one_le_two_pow
      · obtain ⟨i, h1, h2⟩ := hK k hk
        have := mono_wO ov n gs hg h0 _ _ (hlen k) (hlen (k + 1)) (hX k (k + 1) (by omega)) i h1
        rw [h2] at this; exact absurd this (by simp)
    set F := (Finset.range gs.length).filter
      (fun j => isNotOp (gs.getD j ⟨GateOp.or, []⟩).op = true ∧ (ov (n + j)).isNone = true) with hF
    have hne : F.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]; intro he; apply h0; unfold actN; rw [← hF, he]; rfl
    set p := F.min' hne with hpdef
    have hpF : p ∈ F := F.min'_mem hne
    have hpmin : ∀ j ∈ F, p ≤ j := fun j hj => F.min'_le j hj
    have hpF' := hpF
    simp only [hF, Finset.mem_filter, Finset.mem_range] at hpF'
    obtain ⟨hplt, hpnot, hpnone⟩ := hpF'
    have hpnone' : ov (n + p) = none := by simpa using hpnone
    have hgp : gs.getD p ⟨GateOp.or, []⟩ = gs[p] := List.getD_eq_getElem _ _ hplt
    rw [hgp] at hpnot
    have hop := isNotOp_eq hpnot

    have hpre0 : actN ov n (gs.take p) = 0 := by
      unfold actN
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_range, List.length_take] at hj
      have hjp : j < p := by omega
      have : j ∈ F := by
        simp only [hF, Finset.mem_filter, Finset.mem_range]
        refine ⟨by omega, ?_⟩
        have e : (gs.take p).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
          simp [List.getD_eq_getElem?_getD, List.getElem?_take, hjp]
        rw [← e]; exact hj.2
      have := hpmin j this; omega
    have hgpre : ∀ g ∈ gs.take p, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not :=
      fun g hgm => hg g (List.mem_of_mem_take hgm)
    let val : ℕ → Bool := fun k => (wO ov gs (X k)).getD (n + p) false
    have hval : ∀ k, val k = GateOp.not.eval
        (gs[p].inputs.map fun i => (wO ov (gs.take p) (X k)).getD i false) := by
      intro k
      have htake : gs.take (p + 1) = gs.take p ++ [gs[p]] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hplt]; rfl
      have hsplit : gs = gs.take (p + 1) ++ gs.drop (p + 1) := (List.take_append_drop _ _).symm
      have e1 := wO_prefix ov (gs.take (p + 1)) (gs.drop (p + 1)) (X k) (n + p)
        (by rw [hlen]; simp; omega)
      rw [← hsplit] at e1
      show (wO ov gs (X k)).getD (n + p) false = _
      rw [e1, htake]
      have := wO_last ov (gs.take p) gs[p] (X k)
      have hl : (gs.take p).length = p := by simp; omega
      rw [hl, hlen, hpnone'] at this
      rw [this, hop]
    have hanti : ∀ k l, k ≤ l → val l = true → val k = true := by
      intro k l hkl hl
      rw [hval] at hl ⊢
      rcases hin : gs[p].inputs with _ | ⟨i, t⟩
      · simp [GateOp.eval]
      · rw [hin] at hl
        simp only [GateOp.eval, List.map_cons, List.headD_cons, Bool.not_eq_true'] at hl ⊢
        by_contra hc
        simp only [Bool.not_eq_false] at hc
        have := mono_wO ov n (gs.take p) hgpre hpre0 _ _ (hlen k) (hlen l) (hX k l hkl) i hc
        rw [hl] at this; exact absurd this (by simp)
    let ov1 := Function.update ov (n + p) (some true)
    let ov0 := Function.update ov (n + p) (some false)
    have ha1 : actN ov1 n gs ≤ r := by show actN (Function.update ov (n + p) (some true)) n gs ≤ r; have := actN_update ov n gs p hpF true; omega
    have ha0 : actN ov0 n gs ≤ r := by show actN (Function.update ov (n + p) (some false)) n gs ≤ r; have := actN_update ov n gs p hpF false; omega
    have hw : ∀ k, wO (Function.update ov (n + p) (some (val k))) gs (X k) = wO ov gs (X k) :=
      fun k => agree ov gs (X k) (n + p) (val k) hpnone' rfl
    let K1 := K.filter (fun k => val k = true ∧ val (k + 1) = true)
    let K0 := K.filter (fun k => val k = false ∧ val (k + 1) = false)
    let Kc := K.filter (fun k => val k ≠ val (k + 1))
    have hK1 : K1.card + 1 ≤ 2 ^ r := by
      apply ih ov1 ha1 K1
      intro k hk
      simp only [K1, Finset.mem_filter] at hk
      obtain ⟨i, h1, h2⟩ := hK k hk.1
      refine ⟨i, ?_, ?_⟩
      · have := hw k; rw [hk.2.1] at this; show (wO ov1 gs (X k)).getD i false = true
        rw [this]; exact h1
      · have := hw (k + 1); rw [hk.2.2] at this; show (wO ov1 gs (X (k + 1))).getD i false = false
        rw [this]; exact h2
    have hK0 : K0.card + 1 ≤ 2 ^ r := by
      apply ih ov0 ha0 K0
      intro k hk
      simp only [K0, Finset.mem_filter] at hk
      obtain ⟨i, h1, h2⟩ := hK k hk.1
      refine ⟨i, ?_, ?_⟩
      · have := hw k; rw [hk.2.1] at this; show (wO ov0 gs (X k)).getD i false = true
        rw [this]; exact h1
      · have := hw (k + 1); rw [hk.2.2] at this; show (wO ov0 gs (X (k + 1))).getD i false = false
        rw [this]; exact h2
    have hKc : Kc.card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      simp only [Kc, Finset.mem_filter] at ha hb
      have key : ∀ c, val c ≠ val (c + 1) → val c = true ∧ val (c + 1) = false := by
        intro c hc
        cases h : val (c + 1)
        · cases h' : val c
          · rw [h, h'] at hc; exact absurd rfl hc
          · exact ⟨rfl, rfl⟩
        · have := hanti c (c + 1) (by omega) h; rw [this, h] at hc; exact absurd rfl hc
      obtain ⟨a1, a2⟩ := key a ha.2
      obtain ⟨b1, b2⟩ := key b hb.2
      by_contra hab
      rcases Nat.lt_or_gt_of_ne hab with h | h
      · have := hanti (a + 1) b (by omega) b1; rw [a2] at this; exact absurd this (by simp)
      · have := hanti (b + 1) a (by omega) a1; rw [b2] at this; exact absurd this (by simp)
    have hsub : K ⊆ K1 ∪ K0 ∪ Kc := by
      intro k hk
      simp only [K1, K0, Kc, Finset.mem_union, Finset.mem_filter]
      cases h1 : val k <;> cases h2 : val (k + 1) <;> simp [hk]
    have := Finset.card_le_card hsub
    have h3 := Finset.card_union_le (K1 ∪ K0) Kc
    have h4 := Finset.card_union_le K1 K0
    rw [pow_succ]
    omega

theorem cnt_not (inst : ∀ g : Gate, Decidable (g.op = GateOp.not)) (gs : List Gate) :
    ((Finset.range gs.length).filter
      (fun j => isNotOp (gs.getD j ⟨GateOp.or, []⟩).op = true)).card =
      (gs.filter (fun g => @decide (g.op = GateOp.not) (inst g))).length := by
  induction gs using List.reverseRecOn with
  | nil => simp
  | append_singleton gs g ih =>
    have e : (Finset.range (gs ++ [g]).length).filter
        (fun j => isNotOp ((gs ++ [g]).getD j ⟨GateOp.or, []⟩).op = true) =
        if isNotOp g.op = true then insert gs.length ((Finset.range gs.length).filter
          (fun j => isNotOp (gs.getD j ⟨GateOp.or, []⟩).op = true))
        else (Finset.range gs.length).filter
          (fun j => isNotOp (gs.getD j ⟨GateOp.or, []⟩).op = true) := by
      rw [List.length_append, List.length_singleton, Finset.range_add_one, Finset.filter_insert,
        List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero]
      have e2 : (Finset.range gs.length).filter
          (fun j => isNotOp ((gs ++ [g]).getD j ⟨GateOp.or, []⟩).op = true) =
          (Finset.range gs.length).filter
          (fun j => isNotOp (gs.getD j ⟨GateOp.or, []⟩).op = true) := by
        apply Finset.filter_congr
        intro j hj
        rw [Finset.mem_range] at hj
        rw [List.getD_append _ _ _ _ hj]
      rw [e2]
    rw [e, List.filter_append, List.length_append, ← ih]
    cases hg : g.op <;> simp [isNotOp, hg]

theorem actN_none (n : ℕ) (gs : List Gate) :
    actN (fun _ => none) n gs ≤ PEqualNP.NotBracket.notCount ⟨gs, 0⟩ := by
  unfold PEqualNP.NotBracket.notCount actN
  rw [← cnt_not]
  apply le_of_eq
  congr 1
  apply Finset.filter_congr
  intro j _
  simp

theorem getD_chain (m : ℕ) (f : Fin m → Bool) (i : ℕ) :
    (List.ofFn f ++ [false, true]).getD i false =
      if h : i < m then f ⟨i, h⟩ else decide (i = m + 1) := by
  by_cases h : i < m
  · rw [dif_pos h, List.getD_append _ _ _ _ (by simp; exact h)]
    simp [List.getD_eq_getElem?_getD, h]
  · rw [dif_neg h, List.getD_append_right _ _ _ _ (by simp; omega)]
    simp only [List.length_ofFn]
    rcases Nat.lt_trichotomy (i - m) 1 with h1 | h1 | h1
    · have : i = m := by omega
      subst this; simp
    · have : i = m + 1 := by omega
      subst this; simp
    · rw [List.getD_eq_default _ _ (by simp; omega)]
      simp; omega

theorem lower (m a r : ℕ) (C : Circuit) (tap : Fin m → Fin (m + 2 + C.size))
    (hfan : PEqualNP.MetaComplexity.FanInTwo C) (hnot : PEqualNP.NotBracket.notCount C ≤ r)
    (hinv : ∀ x : Fin m → Bool,
      ((Finset.univ : Finset (Fin m)).filter (fun i => x i = false)).card ≤ a →
      ∀ i, (C.wires (List.ofFn x ++ [false,true])).getD (tap i).val false = !x i) :
    min a m < 2 ^ r := by
  classical
  by_contra hcon
  push Not at hcon
  set b := min a m with hb
  have hbm : b ≤ m := min_le_right _ _
  have hba : b ≤ a := min_le_left _ _
  let xs : ℕ → Fin m → Bool := fun k i => decide (b ≤ i.val + k)
  let X : ℕ → List Bool := fun k => List.ofFn (xs k) ++ [false, true]
  have hlen : ∀ k, (X k).length = m + 2 := by intro k; simp [X]
  have hX : ∀ k l, k ≤ l → LeW (X k) (X l) := by
    intro k l hkl i hi
    simp only [X, getD_chain] at hi ⊢
    split_ifs at hi ⊢ with h
    · simp only [xs, decide_eq_true_eq] at hi ⊢; omega
    · exact hi
  have hg : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := by
    intro g hgm
    have := (hfan g hgm).1
    simpa using this
  have hwires : ∀ y, C.wires y = wO (fun _ => none) C.gates y := fun y => rfl
  have hact : actN (fun _ => none) (m + 2) C.gates ≤ r := by
    have := actN_none (m + 2) C.gates
    exact le_trans this hnot
  have hprom : ∀ k, ((Finset.univ : Finset (Fin m)).filter (fun i => xs k i = false)).card ≤ a := by
    intro k
    refine le_trans ?_ hba
    have := Finset.card_le_card_of_injOn (fun i : Fin m => i.val)
      (s := (Finset.univ : Finset (Fin m)).filter (fun i => xs k i = false)) (t := Finset.range b)
      (by intro i hi; simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and,
            xs, decide_eq_false_iff_not] at hi; simp; omega)
      (by intro i _ j _ h; exact Fin.ext h)
    simpa using this
  have hK : ∀ k ∈ Finset.range b, Dec (fun _ => none) C.gates X k := by
    intro k hk
    rw [Finset.mem_range] at hk
    have hi : b - k - 1 < m := by omega
    refine ⟨(tap ⟨b - k - 1, hi⟩).val, ?_, ?_⟩
    · rw [← hwires]; simp only [X]
      rw [hinv (xs k) (hprom k)]
      simp [xs]; omega
    · rw [← hwires]; simp only [X]
      rw [hinv (xs (k + 1)) (hprom (k + 1))]
      simp [xs]; omega
  have := markov (m + 2) C.gates hg X hlen hX r (fun _ => none) hact (Finset.range b) hK
  simp at this
  omega

namespace GateBridgeN

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (FanInTwo)
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)
open PEqualNP.NotBracket (notCount)

variable {α : Type*}

def Scheduled (n : Nat) (F : α → (Fin n → Bool) → Bool) (k nc : Nat) (S : Set α) : Prop :=
  ∃ gs : List Gate, gs.length = k ∧ notCount ⟨gs, 0⟩ = nc ∧ ReadsBack n ⟨gs, 0⟩ ∧ FanInTwo ⟨gs, 0⟩ ∧
    ∀ a ∈ S, ∃ i : Nat, i < n + k ∧
      ∀ x : Fin n → Bool, ((Circuit.mk gs 0).wires (List.ofFn x)).getD i false = F a x

theorem wireLength (C : Circuit) (w : List Bool) :
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

theorem start {n : Nat} {F : α → (Fin n → Bool) → Bool}
    (input : Fin n → α) (h : ∀ i x, F (input i) x = x i) :
    Scheduled n F 0 0 (Set.range input) := by
  refine ⟨[], rfl, rfl, ?_, ?_, ?_⟩
  · simp [ReadsBack]
  · simp [FanInTwo]
  · intro a ha
    obtain ⟨i, rfl⟩ := Set.mem_range.mp ha
    refine ⟨i.val, by simp, fun x => ?_⟩
    change (List.ofFn x).getD i.val false = F (input i) x
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn, h i x]

theorem restrict {n k nc : Nat} {F : α → (Fin n → Bool) → Bool} {S T : Set α}
    (h : Scheduled n F k nc S) (hsub : T ⊆ S) : Scheduled n F k nc T := by
  obtain ⟨gs, hs, hnc, hr, hf, hw⟩ := h
  exact ⟨gs, hs, hnc, hr, hf, fun a ha => hw a (hsub ha)⟩

theorem realizeDeps {n k : Nat} {F : α → (Fin n → Bool) → Bool} {S : Set α}
    {gs : List Gate}
    (hw : ∀ a ∈ S, ∃ i : Nat, i < n + k ∧
      ∀ x : Fin n → Bool, ((Circuit.mk gs 0).wires (List.ofFn x)).getD i false = F a x)
    (deps : List α) (hdeps : ∀ a ∈ deps, a ∈ S) :
    ∃ is : List Nat, is.length = deps.length ∧ (∀ i ∈ is, i < n + k) ∧
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

def isNotGate : GateOp → Nat
  | .not => 1
  | _ => 0

theorem push {n k nc : Nat} {F : α → (Fin n → Bool) → Bool} {S : Set α}
    (h : Scheduled n F k nc S) (op : GateOp) (deps : List α) (out : α)
    (hop : op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hlen : deps.length ≤ 2) (hdeps : ∀ a ∈ deps, a ∈ S)
    (hval : ∀ x, F out x = op.eval (deps.map fun a => F a x)) :
    Scheduled n F (k + 1) (nc + isNotGate op) (insert out S) := by
  obtain ⟨gs, hgs, hnc, hr, hf, hw⟩ := h
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
  have hnc_new : notCount ⟨gs ++ [g], 0⟩ = nc + isNotGate op := by
    dsimp only [notCount] at hnc ⊢
    rw [List.filter_append, List.length_append, hnc, List.filter_cons, List.filter_nil]
    cases op <;> rfl
  refine ⟨gs ++ [g], by simp [hgs], hnc_new, ?_, ?_, ?_⟩
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

end GateBridgeN

namespace Build068

open PEqualNP.CircuitLowerBounds

variable {n : Nat}
abbrev Sig (n : Nat) := (Fin n → Bool) → Bool

def BuildN (A B : Set (Sig n)) (b nb : Nat) : Prop :=
  True ∧ (∀ {m mn S}, GateBridgeN.Scheduled n id m mn S → A ⊆ S →
    ∃ c ≤ b, ∃ cn ≤ nb, GateBridgeN.Scheduled n id (m + c) (mn + cn) (S ∪ B))

theorem BuildN.run {A B : Set (Sig n)} {b nb m mn S} (H : BuildN A B b nb)
    (HS : GateBridgeN.Scheduled n id m mn S) (hA : A ⊆ S) :
    ∃ c ≤ b, ∃ cn ≤ nb, GateBridgeN.Scheduled n id (m + c) (mn + cn) (S ∪ B) := H.2 HS hA

theorem idle {A B : Set (Sig n)} (h : B ⊆ A) : BuildN A B 0 0 := by
  refine ⟨trivial, ?_⟩
  intro m mn S HS hA
  refine ⟨0, Nat.le_refl _, 0, Nat.le_refl _, ?_⟩
  simpa [Set.union_eq_left.mpr (h.trans hA)] using HS

theorem relax {A B C D : Set (Sig n)} {b d nb nd : Nat}
    (H : BuildN A B b nb) (hA : A ⊆ C) (hB : D ⊆ B) (h : b ≤ d) (hn : nb ≤ nd) : BuildN C D d nd := by
  refine ⟨trivial, ?_⟩
  intro m mn S HS hC
  obtain ⟨c, hc, cn, hcn, HS'⟩ := H.run HS (hA.trans hC)
  exact ⟨c, hc.trans h, cn, hcn.trans hn, GateBridgeN.restrict HS' (Set.union_subset_union le_rfl hB)⟩

theorem seq {A B C : Set (Sig n)} {b c nb nc : Nat}
    (H : BuildN A B b nb) (J : BuildN (A ∪ B) C c nc) : BuildN A (B ∪ C) (b + c) (nb + nc) := by
  refine ⟨trivial, ?_⟩
  intro m mn S HS hA
  obtain ⟨d, hd, dn, hdn, K⟩ := H.run HS hA
  obtain ⟨e, he, en, hen, K'⟩ := J.run K (Set.union_subset_union hA le_rfl)
  exact ⟨d + e, Nat.add_le_add hd he, dn + en, Nat.add_le_add hdn hen,
    by simpa [Nat.add_assoc, Set.union_assoc] using K'⟩

theorem one {A : Set (Sig n)} (op : GateOp) (deps : List (Sig n))
    (hop : op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) (hlen : deps.length ≤ 2)
    (hd : ∀ g ∈ deps, g ∈ A) (f : Sig n)
    (hv : ∀ x, f x = op.eval (deps.map fun g => g x)) :
    BuildN A {f} 1 (GateBridgeN.isNotGate op) := by
  refine ⟨trivial, ?_⟩
  intro m mn S HS hA
  refine ⟨1, le_rfl, GateBridgeN.isNotGate op, le_rfl, ?_⟩
  have h := GateBridgeN.push HS op deps f hop hlen (fun g hg => hA (hd g hg)) hv
  rw [Set.insert_eq] at h
  exact GateBridgeN.restrict h (by intro g hg; exact hg.elim Or.inr Or.inl)

def ban (f g : Sig n) : Sig n := fun x => f x && g x
def bor (f g : Sig n) : Sig n := fun x => f x || g x
def bnt (f : Sig n) : Sig n := fun x => !f x

theorem andG {A : Set (Sig n)} {f g : Sig n} (hf : f ∈ A) (hg : g ∈ A) :
    BuildN A {ban f g} 1 0 :=
  one .and [f, g] (by simp) (by simp) (by simpa using And.intro hf hg) (ban f g) (by simp [GateOp.eval, ban])

theorem orG {A : Set (Sig n)} {f g : Sig n} (hf : f ∈ A) (hg : g ∈ A) :
    BuildN A {bor f g} 1 0 :=
  one .or [f, g] (by simp) (by simp) (by simpa using And.intro hf hg) (bor f g) (by simp [GateOp.eval, bor])

theorem notG {A : Set (Sig n)} {f : Sig n} (hf : f ∈ A) : BuildN A {bnt f} 1 1 :=
  one .not [f] (by simp) (by simp) (by simpa using hf) (bnt f) (by simp [GateOp.eval, bnt])

theorem constG {A : Set (Sig n)} (b : Bool) : BuildN A {fun _ => b} 1 0 := by
  cases b
  · exact one .or [] (by simp) (by simp) (by simp) (fun _ => false) (by intro; rfl)
  · exact one .and [] (by simp) (by simp) (by simp) (fun _ => true) (by intro; rfl)
theorem listBuild {α : Type*} {A : Set (Sig n)} (xs : List α)
    (F : α → Sig n) (c cn : Nat) (H : ∀ a ∈ xs, BuildN A {F a} c cn) :
    BuildN A {f | ∃ a ∈ xs, f = F a} (xs.length * c) (xs.length * cn) := by
  induction xs with
  | nil =>
    exact relax (idle (A := A) (B := ∅) (by simp)) le_rfl (by simp) (by simp) (by simp)
  | cons a xs ih =>
    have h1 := H a List.mem_cons_self
    have h2 := ih (fun b hb => H b (List.mem_cons_of_mem a hb))
    have h2' := relax h2 (C := A ∪ {F a}) Set.subset_union_left le_rfl le_rfl le_rfl
    refine relax (seq h1 h2') le_rfl ?_ ?_ ?_
    · rintro f ⟨b, hb, rfl⟩
      rcases List.mem_cons.mp hb with rfl | hb
      · exact Or.inl rfl
      · exact Or.inr ⟨b, hb, rfl⟩
    · simp only [List.length_cons]
      rw [Nat.succ_mul xs.length, Nat.add_comm]
    · simp only [List.length_cons]
      rw [Nat.succ_mul xs.length, Nat.add_comm]

theorem finG {k : Nat} {A : Set (Sig n)} (F : Fin k → Sig n) (c cn : Nat)
    (H : ∀ i, BuildN A {F i} c cn) : BuildN A (Set.range F) (k * c) (k * cn) := by
  have h := listBuild (List.finRange k) F c cn (fun i _ => H i)
  rw [List.length_finRange] at h
  refine relax h le_rfl ?_ le_rfl le_rfl
  rintro _ ⟨i, rfl⟩
  exact ⟨i, List.mem_finRange i, rfl⟩
end Build068

namespace Construct

open Build068 PEqualNP.CircuitLowerBounds

variable {n : Nat}

theorem step2 {A : Set (Sig n)} {f g h : Sig n} (hf : f ∈ A) (hg : g ∈ A) (hh : h ∈ A) :
    BuildN A {bor h (ban f g)} 2 0 := by
  have h1 := andG hf hg
  have h2 := orG (A := A ∪ {ban f g}) (Or.inl hh) (Or.inr rfl)
  exact relax (seq h1 h2) le_rfl (by intro z hz; exact Or.inr hz) le_rfl le_rfl

theorem rangeBuild {A : Set (Sig n)} (k : Nat) (F : Nat → Sig n) (c cn : Nat)
    (H : ∀ i < k, BuildN A {F i} c cn) :
    BuildN A {f | ∃ i < k, f = F i} (k * c) (k * cn) := by
  have h := listBuild (List.range k) F c cn (fun i hi => H i (List.mem_range.mp hi))
  rw [List.length_range] at h
  refine relax h le_rfl ?_ le_rfl le_rfl
  rintro _ ⟨i, hi, rfl⟩
  exact ⟨i, List.mem_range.mpr hi, rfl⟩

def T : Nat → Nat
  | 0 => 0
  | r + 1 => T r + 4 * 2 ^ r - 3

theorem T_add (r : Nat) : T r + 3 * r = 4 * (2 ^ r - 1) := by
  induction r with
  | zero => simp [T]
  | succ r ih =>
    simp only [T]
    have : 1 ≤ 2 ^ r := Nat.one_le_two_pow
    rw [pow_succ]
    omega

def Srt (L : Nat) (u : Nat → Sig n) (x : Fin n → Bool) : Prop :=
  ∀ i j, i ≤ j → j < L → u i x = true → u j x = true

theorem inverter : ∀ (r : Nat) (A : Set (Sig n)) (u : Nat → Sig n),
    (∀ i < 2 ^ r - 1, u i ∈ A) →
    ∃ nu : Nat → Sig n, BuildN A {f | ∃ i < 2 ^ r - 1, f = nu i} (T r) r ∧
      ∀ x, Srt (2 ^ r - 1) u x → ∀ i < 2 ^ r - 1, nu i x = !(u i x) := by
  intro r
  induction r with
  | zero =>
    intro A u _
    refine ⟨u, relax (idle (A := A) (B := ∅) (by simp)) le_rfl (by
      rintro f ⟨i, hi, _⟩; simp at hi) le_rfl le_rfl, ?_⟩
    intro x _ i hi; simp at hi
  | succ r ih =>
    intro A u hu
    set k := 2 ^ r - 1 with hk
    have hpow : 1 ≤ 2 ^ r := Nat.one_le_two_pow
    have hlen : 2 ^ (r + 1) - 1 = 2 * k + 1 := by rw [pow_succ]; omega
    rw [hlen] at hu ⊢
    let nm : Sig n := bnt (u k)
    have H1 : BuildN A {nm} 1 1 := notG (hu k (by omega))
    let A1 := A ∪ {nm}
    let fd : Nat → Sig n := fun i => bor (u i) (ban (u (k + 1 + i)) nm)
    have H2 : BuildN A1 {f | ∃ i < k, f = fd i} (k * 2) (k * 0) :=
      rangeBuild k fd 2 0 (fun i hi => step2 (Or.inl (hu _ (by omega))) (Or.inr rfl)
        (Or.inl (hu _ (by omega))))
    let A2 := A1 ∪ {f | ∃ i < k, f = fd i}
    obtain ⟨nf, H3, hnf⟩ := ih A2 fd (fun i hi => Or.inr ⟨i, hi, rfl⟩)
    let A3 := A2 ∪ {f | ∃ i < k, f = nf i}
    let nu : Nat → Sig n := fun i =>
      if i < k then bor (nf i) nm else if i = k then nm else ban (nf (i - k - 1)) nm
    have H4 : BuildN A3 {f | ∃ i < k, f = bor (nf i) nm} (k * 1) (k * 0) :=
      rangeBuild k _ 1 0 (fun i hi => orG (Or.inr ⟨i, hi, rfl⟩) (Or.inl (Or.inl (Or.inr rfl))))
    have H5 : BuildN A3 {f | ∃ i < k, f = ban (nf i) nm} (k * 1) (k * 0) :=
      rangeBuild k _ 1 0 (fun i hi => andG (Or.inr ⟨i, hi, rfl⟩) (Or.inl (Or.inl (Or.inr rfl))))
    have H45 := seq H4 (relax H5 (C := A3 ∪ {f | ∃ i < k, f = bor (nf i) nm})
      Set.subset_union_left le_rfl le_rfl le_rfl)
    have Hall := seq (seq (seq H1 H2) (relax H3 (C := A ∪ ({nm} ∪ {f | ∃ i < k, f = fd i}))
      (fun z hz => by simp only [A1, A2, Set.mem_union] at hz ⊢; tauto) le_rfl le_rfl le_rfl))
      (relax H45 (C := A ∪ ({nm} ∪ {f | ∃ i < k, f = fd i} ∪ {f | ∃ i < k, f = nf i}))
      (fun z hz => by simp only [A1, A2, A3, Set.mem_union] at hz ⊢; tauto) le_rfl le_rfl le_rfl)
    refine ⟨nu, relax Hall le_rfl ?_ ?_ ?_, ?_⟩
    · rintro f ⟨i, hi, rfl⟩
      simp only [nu]
      split_ifs with h1 h2
      · exact Or.inr (Or.inl ⟨i, h1, rfl⟩)
      · exact Or.inl (Or.inl (Or.inl rfl))
      · exact Or.inr (Or.inr ⟨i - k - 1, by omega, rfl⟩)
    · simp only [T]; omega
    · omega
    · intro x hs i hi
      have hsk : ∀ j, j < 2 * k + 1 → k ≤ j → u k x = true → u j x = true :=
        fun j hj hkj h => hs k j hkj hj h
      cases hmid : u k x
      ·
        have hlow : ∀ j < k, u j x = false := by
          intro j hj
          cases hj' : u j x
          · rfl
          · have := hs j k (by omega) (by omega) hj'; rw [hmid] at this; exact this.symm
        have hnmx : nm x = true := by simp [nm, bnt, hmid]
        have hfd : ∀ j < k, fd j x = u (k + 1 + j) x := by
          intro j hj; simp [fd, bor, ban, hnmx, hlow j hj]
        have hsrt : Srt k fd x := by
          intro a b hab hb ha
          rw [hfd a (by omega)] at ha; rw [hfd b hb]
          exact hs _ _ (by omega) (by omega) ha
        have hnf' := hnf x hsrt
        simp only [nu]
        split_ifs with h1 h2
        · simp [bor, hnmx, hlow i h1]
        · subst h2; simp [nm, bnt]
        · simp only [ban, hnmx, Bool.and_true]
          rw [hnf' _ (by omega), hfd _ (by omega)]
          congr 3; omega
      · have hnmx : nm x = false := by simp [nm, bnt, hmid]
        have hfd : ∀ j < k, fd j x = u j x := by
          intro j hj; simp [fd, bor, ban, hnmx]
        have hsrt : Srt k fd x := by
          intro a b hab hb ha
          rw [hfd a (by omega)] at ha; rw [hfd b hb]
          exact hs _ _ hab (by omega) ha
        have hnf' := hnf x hsrt
        simp only [nu]
        split_ifs with h1 h2
        · simp only [bor, hnmx, Bool.or_false]; rw [hnf' i h1, hfd i h1]
        · subst h2; simp [nm, bnt]
        · simp only [ban, hnmx, Bool.and_false]
          rw [hsk i hi (by omega) hmid]; rfl

end Construct

namespace Construct2

open Build068 Construct PEqualNP.CircuitLowerBounds

variable {n : Nat}

def ins : List (Sig n) → Sig n → List (Sig n) × Sig n
  | [], c => ([], c)
  | l0 :: ls, c => ((ban l0 c) :: (ins ls (bor l0 c)).1, (ins ls (bor l0 c)).2)

def carriesL : List (Sig n) → Sig n → List (Sig n)
  | [], c => [c]
  | l0 :: ls, c => c :: carriesL ls (bor l0 c)

def rev : List (Sig n) → Sig n → List (Sig n) → Sig n → List (Sig n) × Sig n
  | l0 :: ls, c, nn0 :: nns, ncf =>
    (bor (rev ls (bor l0 c) nns ncf).2 (ban nn0 c) :: (rev ls (bor l0 c) nns ncf).1,
      bor (rev ls (bor l0 c) nns ncf).2 (ban nn0 l0))
  | _, _, _, ncf => ([], ncf)

theorem ins_len (l : List (Sig n)) (c : Sig n) : (ins l c).1.length = l.length := by
  induction l generalizing c with
  | nil => rfl
  | cons a l ih => simp [ins, ih]

theorem rev_len (l : List (Sig n)) (c : Sig n) (nns : List (Sig n)) (ncf : Sig n)
    (h : nns.length = l.length) : (rev l c nns ncf).1.length = l.length := by
  induction l generalizing c nns with
  | nil => cases nns <;> rfl
  | cons a l ih =>
    cases nns with
    | nil => simp at h
    | cons b nns => simp only [rev, List.length_cons]; rw [ih _ _ (by simpa using h)]

theorem ins_last_mem (l : List (Sig n)) (c : Sig n) : (ins l c).2 ∈ carriesL l c := by
  induction l generalizing c with
  | nil => simp [ins, carriesL]
  | cons a l ih => simp only [ins, carriesL]; exact List.mem_cons_of_mem _ (ih _)

theorem ins_build {A : Set (Sig n)} (l : List (Sig n)) (c : Sig n)
    (hl : ∀ f ∈ l, f ∈ A) (hc : c ∈ A) :
    BuildN A {f | f ∈ carriesL l c ∨ f ∈ (ins l c).1} (2 * l.length) 0 := by
  induction l generalizing A c with
  | nil =>
    refine relax (idle (A := A) (B := {c}) (by simpa using hc)) le_rfl ?_ le_rfl le_rfl
    intro f hf; simp [carriesL, ins] at hf; simp [hf]
  | cons a l ih =>
    have ha : a ∈ A := hl a (by simp)
    have h1 := andG ha hc
    have h2 := orG (A := A ∪ {ban a c}) (Or.inl ha) (Or.inl hc)
    have h12 := seq h1 h2
    have h3 := ih (A := A ∪ ({ban a c} ∪ {bor a c})) (c := bor a c)
      (fun f hf => Or.inl (hl f (by simp [hf]))) (Or.inr (Or.inr rfl))
    have h0 := idle (A := A) (B := {c}) (by simpa using hc)
    have hall := seq h0 (relax (seq h12 h3) (C := A ∪ {c}) Set.subset_union_left le_rfl le_rfl le_rfl)
    refine relax hall le_rfl ?_ ?_ le_rfl
    · intro f hf
      simp only [carriesL, ins, List.mem_cons, Set.mem_setOf_eq] at hf
      simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq]
      rcases hf with (rfl | hf) | (rfl | hf)
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (Or.inl hf))
      · exact Or.inr (Or.inl (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr hf))
    · simp only [List.length_cons]; omega

end Construct2

namespace Construct2

open Build068 Construct PEqualNP.CircuitLowerBounds

variable {n : Nat}

theorem rev_build {A : Set (Sig n)} (l : List (Sig n)) (c : Sig n) (nns : List (Sig n))
    (ncf : Sig n) (hl : ∀ f ∈ l, f ∈ A) (hcar : ∀ f ∈ carriesL l c, f ∈ A)
    (hnns : ∀ f ∈ nns, f ∈ A) (hncf : ncf ∈ A) (hlen : nns.length = l.length) :
    BuildN A {f | f ∈ (rev l c nns ncf).1 ∨ f = (rev l c nns ncf).2} (4 * l.length) 0 := by
  induction l generalizing c nns with
  | nil =>
    refine relax (idle (A := A) (B := {ncf}) (by simpa using hncf)) le_rfl ?_ le_rfl le_rfl
    intro f hf
    cases nns <;> simp [rev] at hf <;> simp [hf]
  | cons a l ih =>
    cases nns with
    | nil => simp at hlen
    | cons b nns =>
      have hc : c ∈ A := hcar c (by simp [carriesL])
      have ha : a ∈ A := hl a (by simp)
      have hb : b ∈ A := hnns b (by simp)
      have H1 := ih (bor a c) nns (fun f hf => hl f (by simp [hf]))
        (fun f hf => hcar f (by simp [carriesL, hf])) (fun f hf => hnns f (by simp [hf]))
        (by simpa using hlen)
      set R := rev l (bor a c) nns ncf with hR
      let RS := {f | f ∈ R.1 ∨ f = R.2}
      have H2 := step2 (A := A ∪ RS) (f := b) (g := c) (h := R.2) (Or.inl hb) (Or.inl hc)
        (Or.inr (Or.inr rfl))
      have H3 := step2 (A := A ∪ RS ∪ {bor R.2 (ban b c)}) (f := b) (g := a) (h := R.2)
        (Or.inl (Or.inl hb)) (Or.inl (Or.inl ha)) (Or.inl (Or.inr (Or.inr rfl)))
      have H := seq H1 (relax (seq H2 H3) (C := A ∪ RS) le_rfl le_rfl le_rfl le_rfl)
      refine relax H le_rfl ?_ ?_ le_rfl
      · intro f hf
        simp only [rev, ← hR, List.mem_cons, Set.mem_setOf_eq] at hf
        simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq, RS]
        rcases hf with (rfl | hf) | rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inl (Or.inl hf)
        · exact Or.inr (Or.inr rfl)
      · simp only [List.length_cons]; omega

theorem ins_last (l : List (Sig n)) (c : Sig n) (x : Fin n → Bool) :
    (ins l c).2 x = (c x || l.any (fun f => f x)) := by
  induction l generalizing c with
  | nil => simp [ins]
  | cons a l ih =>
    simp only [ins, ih, bor, List.any_cons]
    cases a x <;> cases c x <;> simp

theorem ins_count (l : List (Sig n)) (c : Sig n) (x : Fin n → Bool) :
    (((ins l c).1 ++ [(ins l c).2]).map (fun f => f x)).count false =
      (l.map (fun f => f x)).count false + (if c x then 0 else 1) := by
  induction l generalizing c with
  | nil => cases h : c x <;> simp [ins, h]
  | cons a l ih =>
    have := ih (bor a c)
    simp only [ins, List.cons_append, List.map_cons, List.count_cons] at this ⊢
    rw [this]
    cases ha : a x <;> cases hc : c x <;> simp [ban, bor, ha, hc] <;> omega

theorem ins_allTrue (l : List (Sig n)) (c : Sig n) (x : Fin n → Bool)
    (hl : ∀ f ∈ l, f x = true) (hc : c x = true) :
    ∀ y ∈ ((ins l c).1 ++ [(ins l c).2]).map (fun f => f x), y = true := by
  induction l generalizing c with
  | nil => simp [ins, hc]
  | cons a l ih =>
    have ha : a x = true := hl a (by simp)
    intro y hy
    simp only [ins, List.cons_append, List.map_cons, List.mem_cons] at hy
    rcases hy with rfl | hy
    · simp [ban, ha, hc]
    · exact ih (bor a c) (fun f hf => hl f (by simp [hf])) (by simp [bor, ha]) y hy

theorem ins_sorted (l : List (Sig n)) (c : Sig n) (x : Fin n → Bool)
    (hl : (l.map (fun f => f x)).Pairwise (· ≤ ·)) :
    (((ins l c).1 ++ [(ins l c).2]).map (fun f => f x)).Pairwise (· ≤ ·) := by
  induction l generalizing c with
  | nil => simp [ins]
  | cons a l ih =>
    simp only [List.map_cons, List.pairwise_cons] at hl
    simp only [ins, List.cons_append, List.map_cons, List.pairwise_cons]
    refine ⟨?_, ih (bor a c) hl.2⟩
    intro y hy
    cases hac : ban a c x
    · exact Bool.false_le _
    · simp only [ban, Bool.and_eq_true] at hac
      have hlt : ∀ f ∈ l, f x = true := by
        intro f hf
        have := hl.1 (f x) (List.mem_map_of_mem hf)
        rw [hac.1] at this
        revert this; cases f x <;> simp
      rw [ins_allTrue l (bor a c) x hlt (by simp [bor, hac.1]) y hy]

theorem rev_eval (l : List (Sig n)) (c : Sig n) (nns : List (Sig n)) (ncf : Sig n)
    (x : Fin n → Bool)
    (hn : nns.map (fun f => f x) = ((ins l c).1.map (fun f => f x)).map not)
    (hf : ncf x = !((ins l c).2 x)) :
    (rev l c nns ncf).1.map (fun f => f x) = (l.map (fun f => f x)).map not ∧
      (rev l c nns ncf).2 x = !(c x) := by
  induction l generalizing c nns with
  | nil =>
    cases nns with
    | nil => simp [rev]; simpa [ins] using hf
    | cons b nns => simp [ins] at hn
  | cons a l ih =>
    cases nns with
    | nil => simp [ins] at hn
    | cons b nns =>
      simp only [ins, List.map_cons, List.cons.injEq] at hn
      obtain ⟨hb, hn'⟩ := hn
      obtain ⟨h1, h2⟩ := ih (bor a c) nns hn' (by simpa [ins] using hf)
      simp only [rev, List.map_cons, h1, List.cons.injEq, and_true]
      simp only [bor, ban, h2, hb]
      cases a x <;> cases c x <;> simp

end Construct2

namespace Construct3

open Build068 Construct Construct2 PEqualNP.CircuitLowerBounds

def inp (m : Nat) (i : Nat) : Sig (m + 2) := fun x => if h : i < m + 2 then x ⟨i, h⟩ else false

def restC (m : Nat) (j : Nat) (x : Fin (m + 2) → Bool) : Nat :=
  ((Finset.Ico j m).filter (fun i => inp m i x = false)).card

def costC (m b r j : Nat) : Nat := 6 * ∑ i ∈ Finset.Ico j m, min i b + T r

theorem restC_succ (m j : Nat) (x : Fin (m + 2) → Bool) (hj : j < m) :
    restC m j x = restC m (j + 1) x + (if inp m j x = false then 1 else 0) := by
  unfold restC
  rw [← Finset.insert_Ico_add_one_left_eq_Ico hj, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · rfl

theorem bool_le_true {a b : Bool} (h : a ≤ b) (ha : a = true) : b = true := by
  subst ha; revert h; cases b <;> simp

theorem rest_build (m b r : Nat) (hb : b < 2 ^ r) (hbm : b ≤ m) :
    ∀ d j, j + d = m → ∀ (A : Set (Sig (m + 2))) (L : List (Sig (m + 2))), L.length = min j b →
      (∀ f ∈ L, f ∈ A) → (∀ i < m + 2, inp m i ∈ A) →
      ∃ (NL : List (Sig (m + 2))) (NX : Nat → Sig (m + 2)), NL.length = L.length ∧
        BuildN A {f | f ∈ NL ∨ ∃ i, j ≤ i ∧ i < m ∧ f = NX i} (costC m b r j) r ∧
        ∀ x, inp m (m + 1) x = true → inp m m x = false →
          (L.map (fun f => f x)).Pairwise (· ≤ ·) →
          (L.map (fun f => f x)).count false + restC m j x ≤ b →
          NL.map (fun f => f x) = (L.map (fun f => f x)).map not ∧
          ∀ i, j ≤ i → i < m → NX i x = !(inp m i x) := by
  intro d
  induction d with
  | zero =>
    intro j hj A L hL hLA hinp
    have hjm : j = m := by omega
    subst hjm
    have hLb : L.length = b := by rw [hL]; omega
    let u : Nat → Sig (j + 2) := fun i => L.getD i (inp j (j + 1))
    have hu : ∀ i < 2 ^ r - 1, u i ∈ A := by
      intro i _
      by_cases hi : i < L.length
      · simp only [u, List.getD_eq_getElem _ _ hi]; exact hLA _ (List.getElem_mem hi)
      · simp only [u]; rw [List.getD_eq_default _ _ (show L.length ≤ i by omega)]; exact hinp _ (by omega)
    obtain ⟨nu, H, hnu⟩ := inverter r A u hu
    refine ⟨(List.range L.length).map nu, fun _ => inp j 0, by simp, ?_, ?_⟩
    · refine relax H le_rfl ?_ ?_ le_rfl
      · rintro f (hf | ⟨i, hi1, hi2, _⟩)
        · simp only [List.mem_map, List.mem_range] at hf
          obtain ⟨i, hi, rfl⟩ := hf
          exact ⟨i, by omega, rfl⟩
        · omega
      · simp [costC]
    · intro x hT _ hsort _
      have hsrt : Srt (2 ^ r - 1) u x := by
        intro i k hik hk hui
        by_cases hkl : k < L.length
        · have hil : i < L.length := by omega
          simp only [u, List.getD_eq_getElem _ _ hkl]
          simp only [u, List.getD_eq_getElem _ _ hil] at hui
          rcases Nat.lt_or_eq_of_le hik with hlt | heq
          · have := List.pairwise_iff_getElem.mp hsort i k (by simpa using hil)
              (by simpa using hkl) hlt
            simp only [List.getElem_map] at this
            exact bool_le_true this hui
          · subst heq; exact hui
        · simp only [u]; rw [List.getD_eq_default _ _ (show L.length ≤ k by omega)]; exact hT
      refine ⟨?_, fun i hi1 hi2 => by omega⟩
      apply List.ext_getElem (by simp)
      intro k hk1 hk2
      simp only [List.getElem_map, List.getElem_range]
      simp only [List.length_map, List.length_range] at hk1
      rw [hnu x hsrt k (by omega)]
      simp only [u, List.getD_eq_getElem _ _ hk1]
  | succ d ih =>
    intro j hj A L hL hLA hinp
    have hjm : j < m := by omega
    set c := inp m j with hc
    set P := ins L c with hP
    set L' := if L.length < b then P.1 ++ [P.2] else P.1 with hL'def
    have hP1len : P.1.length = L.length := ins_len L c
    have hL' : L'.length = min (j + 1) b := by
      rw [hL'def]; split_ifs with h
      · simp [hP1len]; omega
      · rw [hP1len]; omega
    have H1 := ins_build L c hLA (hinp j (by omega))
    set I1 := {f | f ∈ carriesL L c ∨ f ∈ P.1} with hI1
    have hL'A : ∀ f ∈ L', f ∈ A ∪ I1 := by
      intro f hf
      rw [hL'def] at hf
      split_ifs at hf
      · rcases List.mem_append.mp hf with hf | hf
        · exact Or.inr (Or.inr hf)
        · rw [List.mem_singleton] at hf; subst hf; exact Or.inr (Or.inl (ins_last_mem L c))
      · exact Or.inr (Or.inr hf)
    obtain ⟨NL', NX', hlen', H2, hcor'⟩ :=
      ih (j + 1) (by omega) (A ∪ I1) L' hL' hL'A (fun i hi => Or.inl (hinp i hi))
    set B2 := {f | f ∈ NL' ∨ ∃ i, j + 1 ≤ i ∧ i < m ∧ f = NX' i} with hB2
    set nns := NL'.take L.length with hnns
    set ncf := if L.length < b then NL'.getD L.length (inp m m) else inp m m with hncf
    have hnnslen : nns.length = L.length := by
      rw [hnns, List.length_take, hlen', hL']; omega
    have H3 := rev_build (A := A ∪ (I1 ∪ B2)) L c nns ncf
      (fun f hf => Or.inl (hLA f hf)) (fun f hf => Or.inr (Or.inl (Or.inl hf)))
      (fun f hf => Or.inr (Or.inr (Or.inl (List.mem_of_mem_take hf))))
      (by
        rw [hncf]; split_ifs with h
        · by_cases hl : L.length < NL'.length
          · rw [List.getD_eq_getElem _ _ hl]
            exact Or.inr (Or.inr (Or.inl (List.getElem_mem hl)))
          · rw [List.getD_eq_default _ _ (by omega)]; exact Or.inl (hinp m (by omega))
        · exact Or.inl (hinp m (by omega)))
      hnnslen
    set R := rev L c nns ncf with hR
    have Hall := seq (seq H1 H2) H3
    refine ⟨R.1, fun i => if i = j then R.2 else NX' i, rev_len L c nns ncf hnnslen,
      relax Hall le_rfl ?_ ?_ (by omega), ?_⟩
    · rintro f (hf | ⟨i, hi1, hi2, rfl⟩)
      · exact Or.inr (Or.inl hf)
      · by_cases hij : i = j
        · simp only [hij, if_true]; exact Or.inr (Or.inr rfl)
        · simp only [hij, if_false]
          exact Or.inl (Or.inr (Or.inr ⟨i, by omega, hi2, rfl⟩))
    · unfold costC
      rw [Finset.sum_eq_sum_Ico_succ_bot hjm]
      rw [hL]; omega
    · intro x hT hF hsort hcount
      have hrs := restC_succ m j x hjm
      rw [← hc] at hrs
      have hcnt := ins_count L c x
      have hsrt := ins_sorted L c x hsort
      have hlast := ins_last L c x
      rw [← hP] at hcnt hsrt hlast
      have hmapP : ((P.1 ++ [P.2]).map (fun f => f x)) =
          P.1.map (fun f => f x) ++ [P.2 x] := by simp

      have hdisc : ¬ L.length < b → P.2 x = true := by
        intro hnb
        rw [hlast]
        by_contra hcon
        simp only [Bool.not_eq_true, Bool.or_eq_false_iff, List.any_eq_false] at hcon
        have hall : (L.map (fun f => f x)).count false = L.length := by
          have : (L.map (fun f => f x)).count false = (L.map (fun f => f x)).length :=
            List.count_eq_length.mpr (by
            intro y hy
            simp only [List.mem_map] at hy
            obtain ⟨f, hf, rfl⟩ := hy
            simpa using (hcon.2 f hf).symm)
          simpa using this
        rw [hall, hrs, hcon.1] at hcount
        simp only [if_true] at hcount
        omega
      have hsort' : (L'.map (fun f => f x)).Pairwise (· ≤ ·) := by
        rw [hL'def]; split_ifs
        · exact hsrt
        · rw [hmapP] at hsrt; exact (List.pairwise_append.mp hsrt).1
      have hcount' : (L'.map (fun f => f x)).count false + restC m (j + 1) x ≤ b := by
        rw [hL'def]; split_ifs with h
        · rw [hcnt]; rw [hrs] at hcount
          cases hcx : c x <;> simp only [hcx, Bool.false_eq_true, if_true, if_false] at hcount ⊢ <;>
            omega
        · rw [hmapP, List.count_append] at hcnt
          have h2 := hdisc h
          rw [h2] at hcnt
          simp only [List.count_singleton, Bool.true_beq, Bool.false_eq_true,
            if_false, add_zero] at hcnt
          rw [hcnt]; rw [hrs] at hcount
          cases hcx : c x <;> simp only [hcx, Bool.false_eq_true, if_true, if_false] at hcount ⊢ <;>
            omega
      obtain ⟨hNL', hNX'⟩ := hcor' x hT hF hsort' hcount'
      have hnnsv : nns.map (fun f => f x) = (P.1.map (fun f => f x)).map not := by
        rw [hnns, List.map_take, hNL', hL'def]
        split_ifs
        · simp only [List.map_append]
          rw [List.take_append_of_le_length (by simp [hP1len])]
          rw [List.take_of_length_le (by simp [hP1len])]
        · rw [List.take_of_length_le (by simp [hP1len])]
      have hncfv : ncf x = !(P.2 x) := by
        rw [hncf]; split_ifs with h
        · have hl : L.length < NL'.length := by rw [hlen', hL']; omega
          rw [List.getD_eq_getElem _ _ hl]
          have e := congrArg (fun l => l[L.length]?) hNL'
          simp only [List.getElem?_map, List.getElem?_eq_getElem hl] at e
          have hl2 : L.length < L'.length := by rw [hL']; omega
          rw [List.getElem?_eq_getElem hl2] at e
          simp only [Option.map_some, Option.some.injEq] at e
          rw [e]
          congr 1
          have e2 : L'[L.length]? = some P.2 := by
            rw [hL'def, if_pos h, List.getElem?_append_right (by simp [hP1len])]
            simp [hP1len]
          rw [List.getElem?_eq_getElem hl2] at e2
          rw [Option.some.injEq] at e2
          rw [e2]
        · rw [hdisc h]; exact hF
      obtain ⟨hR1, hR2⟩ := rev_eval L c nns ncf x hnnsv hncfv
      refine ⟨hR1, ?_⟩
      intro i hi1 hi2
      by_cases hij : i = j
      · subst hij; simp only [if_true]; exact hR2
      · simp only [hij, if_false]; exact hNX' i (by omega) hi2

end Construct3

namespace Final

open Build068 Construct Construct2 Construct3 PEqualNP.CircuitLowerBounds

theorem ofFn_chain (m : Nat) (x : Fin m → Bool) :
    List.ofFn x ++ [false, true] =
      List.ofFn (fun k : Fin (m + 2) => if h : k.val < m then x ⟨k.val, h⟩ else decide (k.val = m + 1)) := by
  apply List.ext_getElem (by simp)
  intro k h1 h2
  have e1 := getD_chain m x k
  rw [List.getD_eq_getElem _ _ h1] at e1
  rw [e1, List.getElem_ofFn]

theorem upper (m a r : Nat) (hb : min a m < 2 ^ r) :
    ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin m → Fin (m + 2 + C.size)),
      (PEqualNP.MetaComplexity.FanInTwo C ∧
        PEqualNP.MetaComplexity.NestedCover.ReadsBack (m + 2) C ∧ C.output < m + 2 + C.size) ∧
      C.size + 3 * r ≤ 6 * (Finset.range m).sum (fun j => min j (min a m)) + 4 * (2 ^ r - 1) ∧
      PEqualNP.NotBracket.notCount C ≤ r ∧
      ∀ x : Fin m → Bool, ((Finset.univ : Finset (Fin m)).filter (fun i => x i = false)).card ≤ a →
        ∀ i, (C.wires (List.ofFn x ++ [false,true])).getD (tap i).val false = !x i := by
  set b := min a m with hbdef
  have hbm : b ≤ m := min_le_right _ _
  let S0 : Set (Sig (m + 2)) := Set.range (fun i : Fin (m + 2) => (fun x => x i : Sig (m + 2)))
  have Hstart : GateBridgeN.Scheduled (m + 2) id 0 0 S0 :=
    GateBridgeN.start (fun i : Fin (m + 2) => (fun x => x i : Sig (m + 2))) (fun _ _ => rfl)
  obtain ⟨NL, NX, _, H, hcor⟩ := rest_build m b r hb hbm m 0 (by omega) S0 [] (by simp) (by simp)
    (fun i hi => ⟨⟨i, hi⟩, by funext x; simp [inp, hi]⟩)
  obtain ⟨c, hc, cn, hcn, HS⟩ := H.run Hstart le_rfl
  obtain ⟨gs, hgs, hnc, hrb, hfan, hw⟩ := HS
  have hex : ∀ i : Fin m, ∃ w : Nat, w < m + 2 + (0 + c) ∧ ∀ x : Fin (m + 2) → Bool,
      ((Circuit.mk gs 0).wires (List.ofFn x)).getD w false = NX i.val x := by
    intro i
    exact hw _ (Or.inr (Or.inr ⟨i.val, by omega, i.isLt, rfl⟩))
  choose w hw1 hw2 using hex
  refine ⟨⟨gs, 0⟩, fun i => ⟨w i, by simp only [Circuit.size, hgs]; exact hw1 i⟩, ⟨hfan, hrb, ?_⟩,
    ?_, ?_, ?_⟩
  · simp [Circuit.size]
  · simp only [Circuit.size, hgs]
    have h1 := T_add r
    unfold costC at hc
    rw [← Finset.range_eq_Ico] at hc
    omega
  · rw [hnc]; omega
  · intro x hprom i
    let x' : Fin (m + 2) → Bool := fun k =>
      if h : k.val < m then x ⟨k.val, h⟩ else decide (k.val = m + 1)
    rw [ofFn_chain m x]
    change ((Circuit.mk gs 0).wires (List.ofFn x')).getD (w i) false = !x i
    rw [hw2 i x']
    have hT : inp m (m + 1) x' = true := by simp [inp, x']
    have hF : inp m m x' = false := by simp [inp, x']
    have hrest : restC m 0 x' ≤ b := by
      unfold restC
      have e : (Finset.Ico 0 m).filter (fun k => inp m k x' = false) =
          ((Finset.univ : Finset (Fin m)).filter (fun i => x i = false)).map Fin.valEmbedding := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_map, Finset.mem_univ, true_and,
          Fin.valEmbedding_apply]
        constructor
        · rintro ⟨⟨_, hk⟩, hx⟩
          refine ⟨⟨k, hk⟩, ?_, rfl⟩
          simpa [inp, x', hk, show k < m + 2 by omega] using hx
        · rintro ⟨j, hj, rfl⟩
          refine ⟨⟨Nat.zero_le _, j.isLt⟩, ?_⟩
          simpa [inp, x', j.isLt, show j.val < m + 2 by omega] using hj
      rw [e, Finset.card_map]
      refine le_min hprom ?_
      exact le_trans (Finset.card_filter_le _ _) (by simp)
    have := (hcor x' hT hF (by simp) (by simpa using hrest)).2 i.val (Nat.zero_le _) i.isLt
    rw [this]
    simp [inp, x', i.isLt, show i.val < m + 2 by omega]

end Final

end PEqualNP.Outside.L_lib_1185

theorem PEqualNP.Outside.L_lib_1185 : (∀ (m a r : Nat),
  let shape := fun (width : Nat) (C : PEqualNP.CircuitLowerBounds.Circuit) =>
    PEqualNP.MetaComplexity.FanInTwo C ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (width + 2) C ∧ C.output < width + 2 + C.size
  let b := min a m
  let S := (Finset.range m).sum (fun j => min j b)
  ((∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin m → Fin (m + 2 + C.size)),
    shape m C ∧ C.size + 3 * r ≤ 6 * S + 4 * (2 ^ r - 1) ∧
    PEqualNP.NotBracket.notCount C ≤ r ∧
    ∀ x : Fin m → Bool, ((Finset.univ : Finset (Fin m)).filter (fun i => x i = false)).card ≤ a →
      ∀ i, (C.wires (List.ofFn x ++ [false,true])).getD (tap i).val false = !x i) ↔ b < 2 ^ r)) := by
  intro m a r shape b S
  constructor
  · rintro ⟨C, tap, hsh, _, hnot, hinv⟩
    exact PEqualNP.Outside.L_lib_1185.lower m a r C tap hsh.1 hnot hinv
  · intro hb
    exact PEqualNP.Outside.L_lib_1185.Final.upper m a r hb
