import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_835

open PEqualNP.CircuitLowerBounds

abbrev F := ZMod 2

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem foldl_step_length (gs : List Gate) :
    ∀ x : List Bool, (gs.foldl step x).length = x.length + gs.length := by
  induction gs with
  | nil => intro x; simp
  | cons g gs ih =>
    intro x
    simp only [List.foldl_cons, ih, step]
    simp
    omega

theorem foldl_step_getD (gs : List Gate) :
    ∀ (x : List Bool) (i : ℕ), i < x.length → (gs.foldl step x).getD i false = x.getD i false := by
  induction gs with
  | nil => intros; rfl
  | cons g gs ih =>
    intro x i hi
    simp only [List.foldl_cons]
    rw [ih _ i (by simp only [step, List.length_append, List.length_singleton]; omega)]
    simp only [step]
    exact List.getD_append _ _ _ _ hi

theorem foldl_step_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    (gs ++ [g]).foldl step x = step (gs.foldl step x) g := by
  simp [List.foldl_append]

theorem step_getD_new (w : List Bool) (g : Gate) :
    (step w g).getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  simp only [step]
  rw [List.getD_append_right _ _ _ _ (le_refl _)]
  simp

theorem step_getD_old (w : List Bool) (g : Gate) (i : ℕ) (hi : i < w.length) :
    (step w g).getD i false = w.getD i false := by
  simp only [step]
  exact List.getD_append _ _ _ _ hi

def bitsN (n : ℕ) (v : Fin n → F) : List Bool := List.ofFn (fun j : Fin n => decide (v j = 1))

theorem bitsN_length (n : ℕ) (v : Fin n → F) : (bitsN n v).length = n := by simp [bitsN]

theorem bitsN_getD (n : ℕ) (v : Fin n → F) (j : ℕ) (hj : j < n) :
    (bitsN n v).getD j false = decide (v ⟨j, hj⟩ = 1) := by
  simp [bitsN, List.getD_eq_getElem?_getD, hj]

def Real (t : ℕ) (ds : List Gate) (f : (Fin t → F) → Bool) : Prop :=
  ∃ n, n < t + ds.length ∧ ∀ z, (ds.foldl step (bitsN t z)).getD n false = f z

def GOk (h : Gate) : Prop :=
  h.inputs.length ≤ 2 ∧ (h.op = GateOp.and ∨ h.op = GateOp.or ∨ h.op = GateOp.mod 2 ∨
    (h.op = GateOp.not ∧ h.inputs.length = 1))

def LegalG (t : ℕ) (ds : List Gate) : Prop :=
  (∀ j < ds.length, ∀ i ∈ (ds.getD j ⟨GateOp.or, []⟩).inputs, i < t + j) ∧ ∀ h ∈ ds, GOk h

noncomputable def costG (ds : List Gate) : ℕ :=
  ds.countP (fun h => @decide ((h.op = GateOp.and ∨ h.op = GateOp.or) ∧ h.inputs.length = 2)
    (Classical.propDecidable _))

theorem costG_snoc_zero (ds : List Gate) (g : Gate)
    (h : ¬((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)) :
    costG (ds ++ [g]) = costG ds := by
  unfold costG
  rw [List.countP_append]
  simp [h]

theorem costG_snoc_one (ds : List Gate) (g : Gate)
    (h : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) :
    costG (ds ++ [g]) = costG ds + 1 := by
  unfold costG
  rw [List.countP_append]
  simp [h]

theorem real_mono {t : ℕ} {ds : List Gate} {f : (Fin t → F) → Bool} (more : List Gate)
    (h : Real t ds f) : Real t (ds ++ more) f := by
  obtain ⟨n, hn, hv⟩ := h
  refine ⟨n, by simp; omega, fun z => ?_⟩
  rw [List.foldl_append, foldl_step_getD more _ n (by rw [foldl_step_length, bitsN_length]; exact hn),
    hv]

theorem real_gate {t : ℕ} {ds : List Gate} (hL : LegalG t ds) (op : GateOp)
    (fs : List ((Fin t → F) → Bool)) (hfs : ∀ f ∈ fs, Real t ds f)
    (hok : ∀ ins : List ℕ, ins.length = fs.length → GOk ⟨op, ins⟩) :
    ∃ g : Gate, g.op = op ∧ g.inputs.length = fs.length ∧ LegalG t (ds ++ [g]) ∧
      Real t (ds ++ [g]) (fun z => op.eval (fs.map fun f => f z)) := by
  classical
  have hc : ∀ f, ∃ n, f ∈ fs → n < t + ds.length ∧
      ∀ z, (ds.foldl step (bitsN t z)).getD n false = f z := by
    intro f
    by_cases hf : f ∈ fs
    · obtain ⟨n, hn, hv⟩ := hfs f hf
      exact ⟨n, fun _ => ⟨hn, hv⟩⟩
    · exact ⟨0, fun h => absurd h hf⟩
  choose τ hτ using hc
  refine ⟨Gate.mk op (fs.map τ), rfl, by simp, ⟨fun j hj i hi => ?_, fun h hh => ?_⟩, ?_⟩
  · simp only [List.length_append, List.length_singleton] at hj
    rcases Nat.lt_or_ge j ds.length with hj' | hj'
    · have e : (ds ++ [Gate.mk op (fs.map τ)]).getD j (Gate.mk GateOp.or []) =
          ds.getD j (Gate.mk GateOp.or []) :=
        List.getD_append _ _ _ _ hj'
      rw [e] at hi
      exact hL.1 j hj' i hi
    · have hjeq : j = ds.length := by omega
      subst hjeq
      have e : (ds ++ [Gate.mk op (fs.map τ)]).getD ds.length (Gate.mk GateOp.or []) =
          Gate.mk op (fs.map τ) := by
        rw [List.getD_append_right _ _ _ _ (le_refl _)]
        simp
      rw [e] at hi
      simp only [List.mem_map] at hi
      obtain ⟨f, hf, rfl⟩ := hi
      exact (hτ f hf).1
  · simp only [List.mem_append, List.mem_singleton] at hh
    rcases hh with hh | rfl
    · exact hL.2 h hh
    · exact hok _ (by simp)
  · refine ⟨t + ds.length, by simp, fun z => ?_⟩
    rw [foldl_step_snoc]
    have hlen : (ds.foldl step (bitsN t z)).length = t + ds.length := by
      rw [foldl_step_length, bitsN_length]
    rw [← hlen, step_getD_new]
    congr 1
    rw [List.map_map]
    apply List.map_congr_left
    intro f hf
    exact (hτ f hf).2 z

theorem real_xor {t : ℕ} {ds : List Gate} (hL : LegalG t ds) (f b : (Fin t → F) → Bool)
    (hf : Real t ds f) (hb : Real t ds b) :
    ∃ ds', LegalG t ds' ∧ costG ds' = costG ds ∧ (∀ h, Real t ds h → Real t ds' h) ∧
      Real t ds' (fun z => xor (f z) (b z)) := by
  obtain ⟨g1, hg1, hl1, hL1, hr1⟩ := real_gate hL (GateOp.mod 2) [f, b]
    (by intro x hx; simp at hx; rcases hx with rfl | rfl <;> assumption)
    (fun ins hins => ⟨show ins.length ≤ 2 by simp at hins; omega, Or.inr (Or.inr (Or.inl rfl))⟩)
  obtain ⟨g2, hg2, hl2, hL2, hr2⟩ := real_gate hL1 GateOp.not [_] (by simpa using hr1)
    (fun ins hins => ⟨show ins.length ≤ 2 by simp at hins; omega,
      Or.inr (Or.inr (Or.inr ⟨rfl, show ins.length = 1 by simpa using hins⟩))⟩)
  refine ⟨ds ++ [g1] ++ [g2], hL2, ?_, fun h hh => real_mono _ (real_mono _ hh), ?_⟩
  · rw [costG_snoc_zero _ _ (by rw [hg2]; simp), costG_snoc_zero _ _ (by rw [hg1]; simp)]
  · obtain ⟨n, hn, hv⟩ := hr2
    refine ⟨n, hn, fun z => ?_⟩
    rw [hv z]
    show GateOp.not.eval [(GateOp.mod 2).eval [f z, b z]] = xor (f z) (b z)
    generalize f z = A
    generalize b z = B
    cases A <;> cases B <;> decide

theorem real_xor_all {t : ℕ} (b : (Fin t → F) → Bool) :
    ∀ (L : List ((Fin t → F) → Bool)) (ds : List Gate), LegalG t ds →
      (∀ f ∈ L, Real t ds f) → Real t ds b →
      ∃ ds', LegalG t ds' ∧ costG ds' = costG ds ∧ (∀ h, Real t ds h → Real t ds' h) ∧
        ∀ f ∈ L, Real t ds' (fun z => xor (f z) (b z)) := by
  intro L
  induction L with
  | nil => intro ds hL _ _; exact ⟨ds, hL, rfl, fun _ h => h, by simp⟩
  | cons f L ih =>
    intro ds hL hfs hb
    obtain ⟨ds1, hL1, hc1, hm1, hx1⟩ :=
      real_xor hL f b (hfs f (List.mem_cons_self ..)) hb
    obtain ⟨ds2, hL2, hc2, hm2, hx2⟩ :=
      ih ds1 hL1 (fun g hg => hm1 g (hfs g (List.mem_cons_of_mem _ hg))) (hm1 b hb)
    refine ⟨ds2, hL2, hc2.trans hc1, fun h hh => hm2 h (hm1 h hh), ?_⟩
    intro g hg
    rcases List.mem_cons.1 hg with rfl | hg
    · exact hm2 _ hx1
    · exact hx2 g hg

theorem dec_add (a b : F) : decide (a + b = 1) = xor (decide (a = 1)) (decide (b = 1)) := by
  fin_cases a <;> fin_cases b <;> decide

def lin {k : ℕ} (s u : Fin k → F) : Bool := decide (dotProduct s u = 1)

theorem lin_add_right {k : ℕ} (s u v : Fin k → F) : lin s (u + v) = xor (lin s u) (lin s v) := by
  simp only [lin, dotProduct_add, dec_add]

theorem lin_add_left {k : ℕ} (s s' u : Fin k → F) : lin (s + s') u = xor (lin s u) (lin s' u) := by
  simp only [lin, add_dotProduct, dec_add]

theorem lin_zero_left {k : ℕ} (u : Fin k → F) : lin (0 : Fin k → F) u = false := by
  simp [lin]

theorem lin_bit_smul {k : ℕ} (s d : Fin k → F) (b : Bool) :
    lin s ((if b then (1 : F) else 0) • d) = (b && lin s d) := by
  cases b <;> simp [lin]

theorem lin_single {k : ℕ} (j : Fin k) (u : Fin k → F) :
    lin (Pi.single j 1) u = decide (u j = 1) := by
  simp [lin, single_dotProduct]

theorem lin_sum {k : ℕ} (ins : List ℕ) (s : ℕ → Fin k → F) (u : Fin k → F) :
    lin (ins.map s).sum u = ins.foldr (fun i acc => xor (lin (s i) u) acc) false := by
  induction ins with
  | nil => simp [lin_zero_left]
  | cons a l ih => simp [List.sum_cons, lin_add_left, ih]

theorem aff_eval (op : GateOp) (ins : List ℕ) (hok : GOk ⟨op, ins⟩)
    (hn : ¬((op = GateOp.and ∨ op = GateOp.or) ∧ ins.length = 2)) (cs ls : ℕ → Bool) :
    op.eval (ins.map fun i => xor (cs i) (ls i)) =
      xor (op.eval (ins.map cs)) (ins.foldr (fun i acc => xor (ls i) acc) false) := by
  obtain ⟨hl, hop⟩ := hok
  simp only at hl hop
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · rcases hop with rfl | rfl | rfl | ⟨rfl, h⟩ <;> simp [GateOp.eval]
  · simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    generalize cs a = A
    generalize ls a = B
    rcases hop with rfl | rfl | rfl | ⟨rfl, _⟩ <;> cases A <;> cases B <;> decide
  · rcases hop with rfl | rfl | rfl | ⟨rfl, h⟩
    · exact absurd ⟨Or.inl rfl, rfl⟩ hn
    · exact absurd ⟨Or.inr rfl, rfl⟩ hn
    · simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
      generalize cs a = A
      generalize ls a = B
      generalize cs b = C
      generalize ls b = D
      cases A <;> cases B <;> cases C <;> cases D <;> decide
    · simp at h
  · simp at hl

structure Piece (k t : ℕ) where
  U : Submodule F (Fin k → F)
  r : ℕ
  e : ℕ
  p : (Fin t → F) → (Fin k → F)
  c : ℕ → (Fin t → F) → Bool
  s : ℕ → (Fin k → F)

def PInv (k t : ℕ) (gs : List Gate) (P : Piece k t) : Prop :=
  Module.finrank F P.U + P.r = k ∧ P.e + P.r ≤ costG gs ∧
  (∃ ds, LegalG t ds ∧ costG ds ≤ P.e ∧ (∀ w < k + t + gs.length, Real t ds (P.c w)) ∧
    ∀ j : Fin k, Real t ds (fun z => decide (P.p z j = 1))) ∧
  ∀ z, ∀ u ∈ P.U, ∀ w < k + t + gs.length,
    (gs.foldl step (bitsN k (P.p z + u) ++ bitsN t z)).getD w false = xor (P.c w z) (lin (P.s w) u)

noncomputable def cnt {k t : ℕ} (L : List (Piece k t)) (z : Fin t → F) (x : Fin k → F) : ℕ :=
  L.countP (fun Q => @decide (x - Q.p z ∈ Q.U) (Classical.propDecidable _))

theorem xin_length (k t : ℕ) (v : Fin k → F) (z : Fin t → F) :
    (bitsN k v ++ bitsN t z).length = k + t := by
  simp [bitsN_length]

theorem cw_old (gs : List Gate) (g : Gate) (x : List Bool) (w : ℕ) (hw : w < x.length + gs.length) :
    ((gs ++ [g]).foldl step x).getD w false = (gs.foldl step x).getD w false := by
  rw [foldl_step_snoc, step_getD_old _ _ _ (by rw [foldl_step_length]; exact hw)]

theorem cw_new (gs : List Gate) (g : Gate) (x : List Bool) :
    ((gs ++ [g]).foldl step x).getD (x.length + gs.length) false =
      g.op.eval (g.inputs.map fun i => (gs.foldl step x).getD i false) := by
  rw [foldl_step_snoc, ← foldl_step_length, step_getD_new]

theorem split_dim {k : ℕ} (U : Submodule F (Fin k → F)) (s d : Fin k → F) (hd : d ∈ U)
    (hsd : dotProduct s d = 1) :
    ∃ U' : Submodule F (Fin k → F), Module.finrank F U' + 1 = Module.finrank F U ∧
      ∀ v, v ∈ U' ↔ v ∈ U ∧ dotProduct s v = 0 := by
  let φ : (Fin k → F) →ₗ[F] F :=
    { toFun := fun v => dotProduct s v
      map_add' := fun a b => dotProduct_add s a b
      map_smul' := fun c a => by simp [dotProduct_smul] }
  let ψ := φ.comp U.subtype
  refine ⟨(LinearMap.ker ψ).map U.subtype, ?_, ?_⟩
  · have h1 := LinearMap.finrank_range_add_finrank_ker ψ
    have hr : LinearMap.range ψ = ⊤ := by
      rw [LinearMap.range_eq_top]
      intro y
      refine ⟨y • ⟨d, hd⟩, ?_⟩
      simp [ψ, φ, dotProduct_smul, hsd]
    rw [hr, finrank_top, Module.finrank_self] at h1
    rw [Submodule.finrank_map_subtype_eq]
    omega
  · intro v
    simp only [Submodule.mem_map, LinearMap.mem_ker, Submodule.coe_subtype]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, hy⟩
    · rintro ⟨hv, h0⟩
      exact ⟨⟨v, hv⟩, h0, rfl⟩

theorem bit_cases (a : F) (b : Bool) : a - (if b then 1 else 0) = 0 ↔ decide (a = 1) = b := by
  fin_cases a <;> cases b <;> decide

theorem pbit_shift {k : ℕ} (v d : Fin k → F) (b : Bool) (j : Fin k) :
    decide ((v + (if b then (1 : F) else 0) • d) j = 1) =
      xor (decide (v j = 1)) (b && decide (d j = 1)) := by
  cases b <;> simp [dec_add]

theorem init_piece (k t : ℕ) : ∃ P : Piece k t, PInv k t [] P ∧ ∀ z x, x - P.p z ∈ P.U := by
  let P : Piece k t :=
    { U := ⊤, r := 0, e := 0, p := fun _ => 0,
      c := fun w z => if w < k then false else
        if h : w - k < t then decide (z ⟨w - k, h⟩ = 1) else false,
      s := fun w => if h : w < k then Pi.single ⟨w, h⟩ 1 else 0 }
  refine ⟨P, ⟨?_, by simp [P, costG], ?_, ?_⟩, fun z x => Submodule.mem_top⟩
  · simp [P]
  · refine ⟨[⟨GateOp.or, []⟩], ⟨fun j hj i hi => ?_, fun h hh => ?_⟩, by simp [costG], ?_, ?_⟩
    · simp at hj; subst hj; simp at hi
    · simp at hh; subst hh; exact ⟨by simp, Or.inr (Or.inl rfl)⟩
    · intro w hw
      simp only [List.length_nil, add_zero] at hw
      by_cases hwk : w < k
      · refine ⟨t, by simp, fun z => ?_⟩
        simp only [P, hwk, if_true, List.foldl_cons, List.foldl_nil]
        have h0 := step_getD_new (bitsN t z) (Gate.mk GateOp.or [])
        rw [bitsN_length] at h0
        rw [h0]
        simp [GateOp.eval]
      · have hwt : w - k < t := by omega
        refine ⟨w - k, by omega, fun z => ?_⟩
        simp only [P, hwk, if_false, hwt, dif_pos]
        rw [List.foldl_cons, List.foldl_nil, step_getD_old _ _ _ (by rw [bitsN_length]; exact hwt),
          bitsN_getD _ _ _ hwt]
    · intro j
      refine ⟨t, by simp, fun z => ?_⟩
      simp only [List.foldl_cons, List.foldl_nil]
      have h0 := step_getD_new (bitsN t z) (Gate.mk GateOp.or [])
      rw [bitsN_length] at h0
      rw [h0]
      simp [P, GateOp.eval]
  · intro z u _ w hw
    simp only [List.length_nil, add_zero] at hw
    simp only [List.foldl_nil, P, zero_add]
    by_cases hwk : w < k
    · rw [List.getD_append _ _ _ _ (by rw [bitsN_length]; exact hwk), bitsN_getD _ _ _ hwk]
      simp [hwk, lin_single]
    · have hwt : w - k < t := by omega
      rw [List.getD_append_right _ _ _ _ (by rw [bitsN_length]; omega), bitsN_length,
        bitsN_getD _ _ _ hwt]
      simp [hwk, hwt, lin_zero_left]

theorem real_congr {t : ℕ} {ds : List Gate} {f f' : (Fin t → F) → Bool} (h : Real t ds f)
    (e : ∀ z, f z = f' z) : Real t ds f' := by
  obtain ⟨n, hn, hv⟩ := h
  exact ⟨n, hn, fun z => (hv z).trans (e z)⟩

theorem gok_len (g : Gate) (hg : GOk g) (ins : List ℕ) (h : ins.length = g.inputs.length) :
    GOk ⟨g.op, ins⟩ := by
  obtain ⟨h1, h2⟩ := hg
  refine ⟨show ins.length ≤ 2 by omega, ?_⟩
  show g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.mod 2 ∨
    (g.op = GateOp.not ∧ ins.length = 1)
  rw [h]; exact h2

theorem real_const {t : ℕ} {ds : List Gate} (hL : LegalG t ds) (β : Bool) :
    ∃ ds', LegalG t ds' ∧ costG ds' = costG ds ∧ (∀ h, Real t ds h → Real t ds' h) ∧
      Real t ds' (fun _ => β) := by
  obtain ⟨g1, hg1, hl1, hL1, hr1⟩ := real_gate hL (if β then GateOp.and else GateOp.or) []
    (by simp) (fun ins hins => ⟨show ins.length ≤ 2 by rw [List.length_nil] at hins; omega,
      by cases β <;> simp⟩)
  refine ⟨ds ++ [g1], hL1, costG_snoc_zero _ _ (by simp at hl1; simp [hl1]),
    fun h hh => real_mono _ hh, real_congr hr1 (fun z => by cases β <;> rfl)⟩

theorem cnt_single_mem {k t : ℕ} (Q : Piece k t) (z : Fin t → F) (x : Fin k → F)
    (h : x - Q.p z ∈ Q.U) : cnt [Q] z x = 1 := by
  simp [cnt, h]

theorem cnt_single_not {k t : ℕ} (Q : Piece k t) (z : Fin t → F) (x : Fin k → F)
    (h : x - Q.p z ∉ Q.U) : cnt [Q] z x = 0 := by
  simp [cnt, h]

theorem step_piece {k t : ℕ} (gs : List Gate) (g : Gate) (hg : GOk g)
    (hin : ∀ i ∈ g.inputs, i < k + t + gs.length) (P : Piece k t) (hP : PInv k t gs P) :
    ∃ L : List (Piece k t), (∀ Q ∈ L, PInv k t (gs ++ [g]) Q) ∧
      ∀ z x, (x - P.p z ∈ P.U → cnt L z x = 1) ∧ (x - P.p z ∉ P.U → cnt L z x = 0) := by
  classical
  obtain ⟨hrank, hcost, ⟨ds, hL, hdc, hcw, hpb⟩, hval⟩ := hP
  set m := k + t + gs.length with hm
  have hlen1 : k + t + (gs ++ [g]).length = m + 1 := by simp [hm]; omega
  have Cold : ∀ v z w, w < m → ((gs ++ [g]).foldl step (bitsN k v ++ bitsN t z)).getD w false =
      (gs.foldl step (bitsN k v ++ bitsN t z)).getD w false := by
    intro v z w hw
    exact cw_old gs g _ w (by rw [xin_length]; omega)
  have Cnew : ∀ v z, ((gs ++ [g]).foldl step (bitsN k v ++ bitsN t z)).getD m false =
      g.op.eval (g.inputs.map fun i => (gs.foldl step (bitsN k v ++ bitsN t z)).getD i false) := by
    intro v z
    have h := cw_new gs g (bitsN k v ++ bitsN t z)
    rw [xin_length] at h
    exact h
  by_cases hbin : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2
  · obtain ⟨hop, hl2⟩ := hbin
    obtain ⟨i1, i2, hgi⟩ : ∃ a b, g.inputs = [a, b] := by
      match h : g.inputs, hl2 with
      | [a, b], _ => exact ⟨a, b, rfl⟩
    have hi1 : i1 < m := hin i1 (by rw [hgi]; simp)
    have hi2 : i2 < m := hin i2 (by rw [hgi]; simp)
    have hcostC : costG (gs ++ [g]) = costG gs + 1 := costG_snoc_one _ _ ⟨hop, hl2⟩
    obtain ⟨A, hA⟩ : ∃ A : Bool, ∀ X Y : Bool,
        g.op.eval [X, Y] = (if A then (X && Y) else (X || Y)) := by
      rcases hop with h | h
      · exact ⟨true, fun X Y => by rw [h]; cases X <;> cases Y <;> rfl⟩
      · exact ⟨false, fun X Y => by rw [h]; cases X <;> cases Y <;> rfl⟩
    by_cases hz : ∀ u ∈ P.U, lin (P.s i1) u = false ∧ lin (P.s i2) u = false
    · obtain ⟨g', hg'op, hg'len, hL', hr'⟩ := real_gate hL g.op [P.c i1, P.c i2]
        (by intro f hf; simp at hf; rcases hf with rfl | rfl; exacts [hcw _ hi1, hcw _ hi2])
        (fun ins hins => gok_len g hg ins (by rw [hins, hl2]; rfl))
      let Q : Piece k t :=
        { U := P.U, r := P.r, e := P.e + 1, p := P.p,
          c := fun w => if w = m then (fun z => g.op.eval [P.c i1 z, P.c i2 z]) else P.c w,
          s := fun w => if w = m then 0 else P.s w }
      refine ⟨[Q], ?_, fun z x => ⟨fun h => cnt_single_mem Q z x h,
        fun h => cnt_single_not Q z x h⟩⟩
      intro Q' hQ'
      simp only [List.mem_singleton] at hQ'
      subst hQ'
      refine ⟨hrank, by simp only [Q]; rw [hcostC]; omega, ⟨ds ++ [g'], hL', ?_, ?_, ?_⟩, ?_⟩
      · simp only [Q]
        rw [costG_snoc_one _ _ ⟨by rw [hg'op]; exact hop, by rw [hg'len]; rfl⟩]
        omega
      · intro w hw
        rw [hlen1] at hw
        by_cases hwm : w = m
        · simp only [Q, hwm, if_true]
          exact real_congr hr' (fun z => by simp)
        · simp only [Q, hwm, if_false]
          exact real_mono _ (hcw w (by omega))
      · intro j; exact real_mono _ (hpb j)
      · intro z u hu w hw
        rw [hlen1] at hw
        by_cases hwm : w = m
        · subst hwm
          simp only [Q, if_true]
          rw [Cnew, hgi]
          simp only [List.map_cons, List.map_nil]
          rw [hval z u hu i1 hi1, hval z u hu i2 hi2, (hz u hu).1, (hz u hu).2, lin_zero_left]
          simp
        · simp only [Q, hwm, if_false]
          rw [Cold _ _ _ (by omega), hval z u hu w (by omega)]
    · push_neg at hz
      obtain ⟨u0, hu0, hne⟩ := hz
      have key : ∀ ia ib, ia < m → ib < m →
          (∀ v z, ((gs ++ [g]).foldl step (bitsN k v ++ bitsN t z)).getD m false =
            (if A then ((gs.foldl step (bitsN k v ++ bitsN t z)).getD ia false &&
              (gs.foldl step (bitsN k v ++ bitsN t z)).getD ib false)
             else ((gs.foldl step (bitsN k v ++ bitsN t z)).getD ia false ||
              (gs.foldl step (bitsN k v ++ bitsN t z)).getD ib false))) →
          ∀ d ∈ P.U, lin (P.s ia) d = true →
          ∃ L : List (Piece k t), (∀ Q ∈ L, PInv k t (gs ++ [g]) Q) ∧
            ∀ z x, (x - P.p z ∈ P.U → cnt L z x = 1) ∧ (x - P.p z ∉ P.U → cnt L z x = 0) := by
        intro ia ib hia hib hCval d hd hdl
        have hsd : dotProduct (P.s ia) d = 1 := of_decide_eq_true hdl
        obtain ⟨U', hU'rank, hU'mem⟩ := split_dim P.U (P.s ia) d hd hsd
        have hU'U : ∀ v, v ∈ U' → v ∈ P.U := fun v hv => ((hU'mem v).1 hv).1
        have hU'lin : ∀ v, v ∈ U' → lin (P.s ia) v = false := by
          intro v hv
          simp [lin, ((hU'mem v).1 hv).2]
        let bf : Bool → (Fin t → F) → Bool := fun β z => xor β (P.c ia z)
        let pass : Bool → Bool := fun β => if A then β else !β
        let child : Bool → Piece k t := fun β =>
          { U := U', r := P.r + 1, e := P.e,
            p := fun z => P.p z + (if bf β z then (1 : F) else 0) • d,
            c := fun w z => if w = m then
                (if pass β then xor (P.c ib z) (bf β z && lin (P.s ib) d) else β)
              else xor (P.c w z) (bf β z && lin (P.s w) d),
            s := fun w => if w = m then (if pass β then P.s ib else 0) else P.s w }
        have hmem : ∀ β z x, (x - (child β).p z ∈ (child β).U ↔
            (x - P.p z ∈ P.U ∧ lin (P.s ia) (x - P.p z) = bf β z)) := by
          intro β z x
          show x - (P.p z + (if bf β z then (1 : F) else 0) • d) ∈ U' ↔ _
          rw [hU'mem, sub_add_eq_sub_sub]
          constructor
          · rintro ⟨h1, h2⟩
            refine ⟨by simpa using P.U.add_mem h1 (P.U.smul_mem (if bf β z then (1 : F) else 0) hd),
              ?_⟩
            rw [dotProduct_sub, dotProduct_smul, hsd, smul_eq_mul, mul_one] at h2
            exact (bit_cases _ _).1 h2
          · rintro ⟨h1, h2⟩
            refine ⟨P.U.sub_mem h1 (P.U.smul_mem _ hd), ?_⟩
            rw [dotProduct_sub, dotProduct_smul, hsd, smul_eq_mul, mul_one]
            exact (bit_cases _ _).2 h2
        have hchild : ∀ β, PInv k t (gs ++ [g]) (child β) := by
          intro β
          refine ⟨?_, ?_, ?_, ?_⟩
          · show Module.finrank F U' + (P.r + 1) = k
            omega
          · show P.e + (P.r + 1) ≤ costG (gs ++ [g])
            rw [hcostC]
            omega
          · obtain ⟨ds1, hL1, hc1, hm1, hb1⟩ : ∃ ds1, LegalG t ds1 ∧ costG ds1 = costG ds ∧
                (∀ h, Real t ds h → Real t ds1 h) ∧ Real t ds1 (bf β) := by
              cases β
              · exact ⟨ds, hL, rfl, fun _ h => h, real_congr (hcw ia hia) (fun z => by simp [bf])⟩
              · obtain ⟨g1, hg1, hl1, hL1', hr1⟩ := real_gate hL GateOp.not [P.c ia]
                  (by simpa using hcw ia hia)
                  (fun ins hins => ⟨show ins.length ≤ 2 by simp at hins; omega,
                    Or.inr (Or.inr (Or.inr ⟨rfl, show ins.length = 1 by simpa using hins⟩))⟩)
                refine ⟨ds ++ [g1], hL1', costG_snoc_zero _ _ (by rw [hg1]; simp),
                  fun _ h => real_mono _ h, real_congr hr1 (fun z => ?_)⟩
                simp [bf, GateOp.eval]
            obtain ⟨ds2, hL2, hc2, hm2, hx2⟩ := real_xor_all (bf β)
              ((List.range m).map P.c ++ (List.finRange k).map (fun j z => decide (P.p z j = 1)))
              ds1 hL1 (by
                intro f hf
                simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_finRange,
                  true_and] at hf
                rcases hf with ⟨w, hw, rfl⟩ | ⟨j, rfl⟩
                · exact hm1 _ (hcw w hw)
                · exact hm1 _ (hpb j)) hb1
            obtain ⟨ds3, hL3, hc3, hm3, hk3⟩ := real_const hL2 β
            refine ⟨ds3, hL3, by show costG ds3 ≤ P.e; omega, ?_, ?_⟩
            · intro w hw
              rw [hlen1] at hw
              have hold : ∀ w, w < m →
                  Real t ds3 (fun z => xor (P.c w z) (bf β z && lin (P.s w) d)) := by
                intro w hw
                cases hlw : lin (P.s w) d
                · exact hm3 _ (hm2 _ (hm1 _ (real_congr (hcw w hw) (fun z => by simp))))
                · exact hm3 _ (real_congr (hx2 (P.c w) (by simp; exact Or.inl ⟨w, hw, rfl⟩))
                    (fun z => by simp))
              by_cases hwm : w = m
              · subst hwm
                show Real t ds3 (fun z => if m = m then _ else _)
                simp only [if_true]
                cases hp : pass β
                · exact real_congr hk3 (fun z => by simp)
                · exact real_congr (hold ib hib) (fun z => by simp)
              · show Real t ds3 (fun z => if w = m then _ else _)
                exact real_congr (hold w (by omega)) (fun z => by simp [hwm])
            · intro j
              show Real t ds3 (fun z => decide ((P.p z + (if bf β z then (1 : F) else 0) • d) j = 1))
              cases hdj : decide (d j = 1)
              · exact hm3 _ (hm2 _ (hm1 _ (real_congr (hpb j)
                  (fun z => by rw [pbit_shift, hdj]; simp))))
              · exact hm3 _ (real_congr (hx2 (fun z => decide (P.p z j = 1)) (by simp))
                  (fun z => by rw [pbit_shift, hdj]; simp))
          · intro z u' hu' w hw
            rw [hlen1] at hw
            have hu : (if bf β z then (1 : F) else 0) • d + u' ∈ P.U :=
              P.U.add_mem (P.U.smul_mem _ hd) (hU'U u' hu')
            have hpt : (child β).p z + u' = P.p z + ((if bf β z then (1 : F) else 0) • d + u') := by
              show P.p z + _ + u' = _
              rw [add_assoc]
            have hold : ∀ w, w < m →
                (gs.foldl step (bitsN k ((child β).p z + u') ++ bitsN t z)).getD w false
                  = xor (xor (P.c w z) (bf β z && lin (P.s w) d)) (lin (P.s w) u') := by
              intro w hw
              rw [hpt, hval z _ hu w hw, lin_add_right, lin_bit_smul, Bool.xor_assoc]
            by_cases hwm : w = m
            · subst hwm
              rw [hCval, hold ia hia, hold ib hib, hdl, hU'lin u' hu']
              show _ = xor (if m = m then (if pass β then _ else β) else _)
                (lin (if m = m then (if pass β then P.s ib else 0) else P.s m) u')
              simp only [if_true]
              have hli : lin (if pass β then P.s ib else 0) u' = (pass β && lin (P.s ib) u') := by
                cases pass β <;> simp [lin_zero_left]
              rw [hli]
              simp only [pass, bf]
              generalize P.c ia z = C1
              generalize P.c ib z = C2
              generalize lin (P.s ib) d = L1
              generalize lin (P.s ib) u' = L2
              cases A <;> cases β <;> cases C1 <;> cases C2 <;> cases L1 <;> cases L2 <;>
                simp [lin_zero_left]
            · rw [Cold _ _ _ (by omega), hold w (by omega)]
              show _ = xor (if w = m then _ else _) (lin (if w = m then _ else P.s w) u')
              simp [hwm]
        refine ⟨[child false, child true], ?_, fun z x => ⟨fun h => ?_, fun h => ?_⟩⟩
        · intro Q hQ
          simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hQ
          rcases hQ with rfl | rfl <;> exact hchild _
        · by_cases hl : lin (P.s ia) (x - P.p z) = bf false z
          · have m0 : x - (child false).p z ∈ (child false).U := (hmem false z x).2 ⟨h, hl⟩
            have m1 : x - (child true).p z ∉ (child true).U := by
              rw [hmem]
              rintro ⟨_, h2⟩
              rw [hl] at h2
              simp [bf] at h2
            simp [cnt, List.countP_cons, m0, m1]
          · have m0 : x - (child false).p z ∉ (child false).U := by
              rw [hmem]; exact fun hh => hl hh.2
            have m1 : x - (child true).p z ∈ (child true).U := by
              rw [hmem]
              refine ⟨h, ?_⟩
              revert hl
              simp only [bf]
              cases lin (P.s ia) (x - P.p z) <;> cases P.c ia z <;> simp
            simp [cnt, List.countP_cons, m0, m1]
        · have m0 : x - (child false).p z ∉ (child false).U := by
            rw [hmem]; exact fun hh => h hh.1
          have m1 : x - (child true).p z ∉ (child true).U := by
            rw [hmem]; exact fun hh => h hh.1
          simp [cnt, List.countP_cons, m0, m1]
      by_cases h1 : lin (P.s i1) u0 = true
      · refine key i1 i2 hi1 hi2 (fun v z => ?_) u0 hu0 h1
        rw [Cnew, hgi]; exact hA _ _
      · have h2 : lin (P.s i2) u0 = true := by
          cases hb : lin (P.s i1) u0
          · exact Bool.eq_true_of_not_eq_false (hne hb)
          · exact absurd hb h1
        refine key i2 i1 hi2 hi1 (fun v z => ?_) u0 hu0 h2
        rw [Cnew, hgi]
        simp only [List.map_cons, List.map_nil]
        rw [hA]
        cases A <;> simp [Bool.and_comm, Bool.or_comm]
  · obtain ⟨g', hg'op, hg'len, hL', hr'⟩ := real_gate hL g.op (g.inputs.map P.c)
      (by intro f hf; simp only [List.mem_map] at hf; obtain ⟨i, hi, rfl⟩ := hf; exact hcw i (hin i hi))
      (fun ins hins => gok_len g hg ins (by rw [hins]; simp))
    let Q : Piece k t :=
      { U := P.U, r := P.r, e := P.e, p := P.p,
        c := fun w => if w = m then (fun z => g.op.eval (g.inputs.map fun i => P.c i z)) else P.c w,
        s := fun w => if w = m then (g.inputs.map P.s).sum else P.s w }
    refine ⟨[Q], ?_, fun z x => ⟨fun h => cnt_single_mem Q z x h,
      fun h => cnt_single_not Q z x h⟩⟩
    intro Q' hQ'
    simp only [List.mem_singleton] at hQ'
    subst hQ'
    refine ⟨hrank, by simp only [Q]; rw [costG_snoc_zero _ _ hbin]; exact hcost,
      ⟨ds ++ [g'], hL', ?_, ?_, ?_⟩, ?_⟩
    · simp only [Q]
      rw [costG_snoc_zero _ _ (by rw [hg'op, hg'len]; simpa using hbin)]
      exact hdc
    · intro w hw
      rw [hlen1] at hw
      by_cases hwm : w = m
      · simp only [Q, hwm, if_true]
        exact real_congr hr' (fun z => by simp only [List.map_map]; rfl)
      · simp only [Q, hwm, if_false]
        exact real_mono _ (hcw w (by omega))
    · intro j; exact real_mono _ (hpb j)
    · intro z u hu w hw
      rw [hlen1] at hw
      by_cases hwm : w = m
      · subst hwm
        simp only [Q, if_true]
        rw [Cnew]
        have e1 : (g.inputs.map fun i => (gs.foldl step (bitsN k (P.p z + u) ++ bitsN t z)).getD i false)
            = g.inputs.map fun i => xor (P.c i z) (lin (P.s i) u) :=
          List.map_congr_left (fun i hi => hval z u hu i (hin i hi))
        rw [e1, aff_eval g.op g.inputs hg hbin (fun i => P.c i z) (fun i => lin (P.s i) u), lin_sum]
      · simp only [Q, hwm, if_false]
        rw [Cold _ _ _ (by omega), hval z u hu w (by omega)]

theorem step_list {k t : ℕ} (gs : List Gate) (g : Gate) (hg : GOk g)
    (hin : ∀ i ∈ g.inputs, i < k + t + gs.length) :
    ∀ L : List (Piece k t), (∀ P ∈ L, PInv k t gs P) →
      ∃ L' : List (Piece k t), (∀ Q ∈ L', PInv k t (gs ++ [g]) Q) ∧
        ∀ z x, cnt L' z x = cnt L z x := by
  intro L
  induction L with
  | nil => intro _; exact ⟨[], by simp, fun z x => rfl⟩
  | cons P L ih =>
    intro hL
    obtain ⟨LP, hLP, hcP⟩ := step_piece gs g hg hin P (hL P (List.mem_cons_self ..))
    obtain ⟨L', hL', hc'⟩ := ih (fun Q hQ => hL Q (List.mem_cons_of_mem _ hQ))
    refine ⟨LP ++ L', fun Q hQ => ?_, fun z x => ?_⟩
    · rcases List.mem_append.1 hQ with h | h
      exacts [hLP Q h, hL' Q h]
    · have e1 : cnt (LP ++ L') z x = cnt LP z x + cnt L' z x := by
        simp only [cnt, List.countP_append]
      rw [e1, hc' z x]
      by_cases hm : x - P.p z ∈ P.U
      · rw [(hcP z x).1 hm]
        simp only [cnt, List.countP_cons]
        simp [hm]
        omega
      · rw [(hcP z x).2 hm]
        simp only [cnt, List.countP_cons]
        simp [hm]

theorem all_gates {k t : ℕ} (C : Circuit) (hC : ∀ h ∈ C.gates, GOk h)
    (hRB : ∀ j < C.gates.length, ∀ i ∈ (C.gates.getD j ⟨GateOp.or, []⟩).inputs, i < k + t + j) :
    ∀ n, n ≤ C.gates.length → ∃ L : List (Piece k t),
      (∀ P ∈ L, PInv k t (C.gates.take n) P) ∧ ∀ z x, cnt L z x = 1 := by
  intro n
  induction n with
  | zero =>
    intro _
    obtain ⟨P, hP, hm⟩ := init_piece k t
    exact ⟨[P], by simpa using hP, fun z x => cnt_single_mem P z x (hm z x)⟩
  | succ n ih =>
    intro hn
    obtain ⟨L, hL, hc⟩ := ih (by omega)
    have hlt : n < C.gates.length := by omega
    have htake : C.gates.take (n + 1) = C.gates.take n ++ [C.gates[n]] := by
      rw [List.take_succ, List.getElem?_eq_getElem hlt]
      rfl
    have e : C.gates.getD n ⟨GateOp.or, []⟩ = C.gates[n] := by
      simp [List.getD_eq_getElem?_getD, hlt]
    obtain ⟨L', hL', hc'⟩ := step_list (C.gates.take n) (C.gates[n]) (hC _ (List.getElem_mem hlt))
      (by
        intro i hi
        have h := hRB n hlt i (by rw [e]; exact hi)
        rw [List.length_take]
        omega) L hL
    exact ⟨L', by rw [htake]; exact hL', fun z x => (hc' z x).trans (hc z x)⟩

theorem exists_unique_of_count {α : Type*} (q : α → Prop) :
    ∀ l : List α, l.countP (fun a => @decide (q a) (Classical.propDecidable _)) = 1 →
      ∃! i : Fin l.length, q (l.get i) := by
  intro l
  induction l with
  | nil => intro h; simp at h
  | cons a l ih =>
    intro h
    rw [List.countP_cons] at h
    by_cases ha : q a
    · have h0 : l.countP (fun a => @decide (q a) (Classical.propDecidable _)) = 0 := by
        have e : (@decide (q a) (Classical.propDecidable _)) = true :=
          @decide_eq_true _ (Classical.propDecidable _) ha
        rw [e, if_pos rfl] at h
        omega
      rw [List.countP_eq_zero] at h0
      refine ⟨⟨0, by simp⟩, by simpa using ha, ?_⟩
      intro j hj
      rcases j with ⟨_ | j, hjl⟩
      · rfl
      · exfalso
        have hj' : q (l.get ⟨j, by simpa using hjl⟩) := by simpa using hj
        have := h0 (l.get ⟨j, by simpa using hjl⟩) (List.get_mem _ _)
        simp only [decide_eq_true_eq] at this
        exact this hj'
    · have h1 : l.countP (fun a => @decide (q a) (Classical.propDecidable _)) = 1 := by
        have e : (@decide (q a) (Classical.propDecidable _)) = false :=
          @decide_eq_false _ (Classical.propDecidable _) ha
        rw [e, if_neg Bool.false_ne_true] at h
        omega
      obtain ⟨i, hi, huniq⟩ := ih h1
      refine ⟨i.succ, by simpa using hi, ?_⟩
      intro j hj
      rcases j with ⟨_ | j, hjl⟩
      · exfalso
        exact ha (by simpa using hj)
      · have := huniq ⟨j, by simpa using hjl⟩ (by simpa using hj)
        apply Fin.ext
        simp only [Fin.val_succ]
        rw [← this]

theorem bit_back (a : F) : (if decide (a = 1) = true then (1 : F) else 0) = a := by
  revert a
  decide

end PEqualNP.Outside.L_lib_835

open PEqualNP.Outside.L_lib_835 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_lib_835 : (∀ (k t : ℕ),
  let Circ := PEqualNP.CircuitLowerBounds.Circuit
  let F := ZMod 2
  let legal := fun (n : ℕ) (C : Circ) =>
    PEqualNP.MetaComplexity.NestedCover.ReadsBack n C ∧
      (∀ h ∈ C.gates, h.inputs.length ≤ 2 ∧
        (h.op = .and ∨ h.op = .or ∨ h.op = .mod 2 ∨ (h.op = .not ∧ h.inputs.length = 1)))
  let cost := fun (C : Circ) => C.gates.countP (fun h => @decide
    ((h.op = .and ∨ h.op = .or) ∧ h.inputs.length = 2) (Classical.propDecidable _))
  let bits := fun (n : ℕ) (u : Fin n → F) => List.ofFn (fun j : Fin n => decide (u j = 1))
  let V := Fin k → F
  let Z := Fin t → F
  ∀ C : Circ, legal (k+t) C →
    ∃ (N : ℕ) (r : Fin N → ℕ) (U : Fin N → Submodule F V) (a : Fin N → V)
      (D : Fin N → Circ) (tap : Fin N → Fin k → ℕ),
      let pos := fun (i : Fin N) (z : Z) (j : Fin k) =>
        if ((D i).wires (bits t z)).getD (tap i j) false then (1 : F) else 0
      0 < N ∧ (∀ i, Module.finrank F (U i) + r i = k ∧ legal t (D i) ∧
        cost (D i)+r i ≤ cost C ∧ (D i).output < t+(D i).size ∧
        ∀ j, tap i j < t+(D i).size) ∧
      (∀ (z : Z) (x : V), ∃! i : Fin N, x-pos i z ∈ U i) ∧
      ∀ (i : Fin N) (z : Z) (u : V), u ∈ U i →
        C.eval (bits k (pos i z+u) ++ bits t z) =
          Bool.xor ((D i).eval (bits t z)) (decide (dotProduct (a i) u = 1))) := by
  intro k t
  dsimp only
  intro C hC
  obtain ⟨hRB, hgates⟩ := hC
  obtain ⟨L, hL, hc⟩ := all_gates (k := k) (t := t) C (fun h hh => hgates h hh)
    (fun j hj i hi => hRB j hj i hi) C.gates.length le_rfl
  rw [List.take_length] at hL
  set M := k + t + C.gates.length with hM
  have hdata : ∀ i : Fin L.length, ∃ (ds : List Gate) (o : ℕ) (tp : Fin k → ℕ),
      LegalG t ds ∧ costG ds ≤ (L.get i).e ∧ o < t + ds.length ∧ (∀ j, tp j < t + ds.length) ∧
      (∀ z, (ds.foldl step (bitsN t z)).getD o false =
        (if C.output < M then (L.get i).c C.output z else false)) ∧
      ∀ j z, (ds.foldl step (bitsN t z)).getD (tp j) false = decide ((L.get i).p z j = 1) := by
    intro i
    obtain ⟨_, _, ⟨ds, hLd, hdc, hcw, hpb⟩, _⟩ := hL (L.get i) (List.get_mem _ _)
    obtain ⟨ds', hL', hc', hm', hk'⟩ := real_const hLd false
    have hout : Real t ds' (fun z => if C.output < M then (L.get i).c C.output z else false) := by
      by_cases ho : C.output < M
      · exact real_congr (hm' _ (hcw _ ho)) (fun z => by simp [ho])
      · exact real_congr hk' (fun z => by simp [ho])
    obtain ⟨o, ho, hov⟩ := hout
    have hp : ∀ j : Fin k, ∃ n, n < t + ds'.length ∧
        ∀ z, (ds'.foldl step (bitsN t z)).getD n false = decide ((L.get i).p z j = 1) :=
      fun j => hm' _ (hpb j)
    choose tp htp using hp
    exact ⟨ds', o, tp, hL', by omega, ho, fun j => (htp j).1, hov, fun j z => (htp j).2 z⟩
  choose ds o tp hds using hdata
  have hposj : ∀ (i : Fin L.length) (z : Fin t → ZMod 2) (j : Fin k),
      (if (({ gates := ds i, output := o i } : Circuit).wires
        (List.ofFn fun j : Fin t => decide (z j = 1))).getD (tp i j) false = true
        then (1 : ZMod 2) else 0) = (L.get i).p z j := by
    intro i z j
    have h := (hds i).2.2.2.2.2 j z
    show (if ((ds i).foldl step (bitsN t z)).getD (tp i j) false = true then (1 : F) else 0) = _
    rw [h, bit_back]
  refine ⟨L.length, fun i => (L.get i).r, fun i => (L.get i).U,
    fun i => if C.output < M then (L.get i).s C.output else 0,
    fun i => ⟨ds i, o i⟩, tp, ?_, ?_, ?_, ?_⟩
  · have h := hc 0 0
    rcases L with _ | ⟨P, L⟩
    · simp [cnt] at h
    · simp
  · intro i
    obtain ⟨hrank, hcost, _, _⟩ := hL (L.get i) (List.get_mem _ _)
    obtain ⟨hLd, hdc, ho, htp, _, _⟩ := hds i
    refine ⟨hrank, ⟨fun j hj i' hi' => hLd.1 j hj i' hi', fun h hh => hLd.2 h hh⟩, ?_, ho, htp⟩
    show costG (ds i) + (L.get i).r ≤ costG C.gates
    omega
  · intro z x
    obtain ⟨i, hi, hu⟩ := exists_unique_of_count (fun Q : Piece k t => x - Q.p z ∈ Q.U) L (hc z x)
    refine ⟨i, ?_, fun j hj => hu j ?_⟩
    · dsimp only
      simp only [hposj]
      exact hi
    · dsimp only at hj
      simp only [hposj] at hj
      exact hj
  · intro i z u hu
    obtain ⟨_, _, _, hval⟩ := hL (L.get i) (List.get_mem _ _)
    have hv := (hds i).2.2.2.2.1 z
    dsimp only
    simp only [hposj]
    show (C.gates.foldl step (bitsN k ((L.get i).p z + u) ++ bitsN t z)).getD C.output false =
      xor (((ds i).foldl step (bitsN t z)).getD (o i) false)
        (decide (dotProduct (if C.output < M then (L.get i).s C.output else 0) u = 1))
    rw [hv]
    by_cases ho : C.output < M
    · rw [hval z u hu _ ho, if_pos ho, if_pos ho]
      rfl
    · rw [if_neg ho, if_neg ho, List.getD_eq_default _ _ (by rw [foldl_step_length, xin_length]; omega)]
      simp
