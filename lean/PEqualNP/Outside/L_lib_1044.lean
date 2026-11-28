import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1044_aux

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

abbrev Piece (k t : ℕ) := Submodule F (Fin k → F) × ℕ × ℕ × ((Fin t → F) → (Fin k → F)) × (ℕ → (Fin t → F) → Bool) × (ℕ → (Fin k → F))

abbrev Piece.U {k t} (P : Piece k t) := P.1
abbrev Piece.r {k t} (P : Piece k t) := P.2.1
abbrev Piece.e {k t} (P : Piece k t) := P.2.2.1
abbrev Piece.p {k t} (P : Piece k t) := P.2.2.2.1
abbrev Piece.c {k t} (P : Piece k t) := P.2.2.2.2.1
abbrev Piece.s {k t} (P : Piece k t) := P.2.2.2.2.2

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
    ⟨⊤, 0, 0, fun _ => 0, fun w z => if w < k then false else
        if h : w - k < t then decide (z ⟨w - k, h⟩ = 1) else false, fun w => if h : w < k then Pi.single ⟨w, h⟩ 1 else 0⟩
  refine ⟨P, ⟨?_, by simp [Piece.U, Piece.r, Piece.e, Piece.p, Piece.c, Piece.s, P, costG], ?_, ?_⟩, fun z x => Submodule.mem_top⟩
  · simp [Piece.U, Piece.r, Piece.e, Piece.p, Piece.c, Piece.s, P]
  · refine ⟨[⟨GateOp.or, []⟩], ⟨fun j hj i hi => ?_, fun h hh => ?_⟩, by simp [costG], ?_, ?_⟩
    · simp at hj; subst hj; simp at hi
    · simp at hh; subst hh; exact ⟨by simp, Or.inr (Or.inl rfl)⟩
    · intro w hw
      simp only [List.length_nil, add_zero] at hw
      by_cases hwk : w < k
      · refine ⟨t, by simp, fun z => ?_⟩
        simp only [Piece.U, Piece.r, Piece.e, Piece.p, Piece.c, Piece.s, P, hwk, if_true, List.foldl_cons, List.foldl_nil]
        have h0 := step_getD_new (bitsN t z) (Gate.mk GateOp.or [])
        rw [bitsN_length] at h0
        rw [h0]
        simp [GateOp.eval]
      · have hwt : w - k < t := by omega
        refine ⟨w - k, by omega, fun z => ?_⟩
        simp only [Piece.U, Piece.r, Piece.e, Piece.p, Piece.c, Piece.s, P, hwk, if_false, hwt, dif_pos]
        rw [List.foldl_cons, List.foldl_nil, step_getD_old _ _ _ (by rw [bitsN_length]; exact hwt),
          bitsN_getD _ _ _ hwt]
    · intro j
      refine ⟨t, by simp, fun z => ?_⟩
      simp only [List.foldl_cons, List.foldl_nil]
      have h0 := step_getD_new (bitsN t z) (Gate.mk GateOp.or [])
      rw [bitsN_length] at h0
      rw [h0]
      simp [Piece.U, Piece.r, Piece.e, Piece.p, Piece.c, Piece.s, P, GateOp.eval]
  · intro z u _ w hw
    simp only [List.length_nil, add_zero] at hw
    simp only [Piece.U, Piece.r, Piece.e, Piece.p, Piece.c, Piece.s, List.foldl_nil, P, zero_add]
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
  have hcost0 := hcost
  have hdc0 := hdc
  dsimp only [Piece.r,Piece.e] at hcost0 hdc0
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
        ⟨P.U, P.r, P.e + 1, P.p, fun w => if w = m then (fun z => g.op.eval [P.c i1 z, P.c i2 z]) else P.c w, fun w => if w = m then 0 else P.s w⟩
      refine ⟨[Q], ?_, fun z x => ⟨fun h => cnt_single_mem Q z x h,
        fun h => cnt_single_not Q z x h⟩⟩
      intro Q' hQ'
      simp only [List.mem_singleton] at hQ'
      subst hQ'
      refine ⟨hrank, by simp only [Piece.U, Piece.r, Piece.e, Piece.p, Piece.c, Piece.s, Q]; rw [hcostC]; omega, ⟨ds ++ [g'], hL', ?_, ?_, ?_⟩, ?_⟩
      · simp only [Piece.U, Piece.r, Piece.e, Piece.p, Piece.c, Piece.s, Q]
        rw [costG_snoc_one _ _ ⟨by rw [hg'op]; exact hop, by rw [hg'len]; rfl⟩]
        omega
      · intro w hw
        rw [hlen1] at hw
        by_cases hwm : w = m
        · simp only [Piece.U, Piece.r, Piece.e, Piece.p, Piece.c, Piece.s, Q, hwm, if_true]
          exact real_congr hr' (fun z => by simp)
        · simp only [Piece.U, Piece.r, Piece.e, Piece.p, Piece.c, Piece.s, Q, hwm, if_false]
          exact real_mono _ (hcw w (by omega))
      · intro j; exact real_mono _ (hpb j)
      · intro z u hu w hw
        rw [hlen1] at hw
        by_cases hwm : w = m
        · subst hwm
          simp only [Piece.U, Piece.r, Piece.e, Piece.p, Piece.c, Piece.s, Q, if_true]
          rw [Cnew, hgi]
          simp only [List.map_cons, List.map_nil]
          rw [hval z u hu i1 hi1, hval z u hu i2 hi2, (hz u hu).1, (hz u hu).2, lin_zero_left]
          simp
        · simp only [Piece.U, Piece.r, Piece.e, Piece.p, Piece.c, Piece.s, Q, hwm, if_false]
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
          ⟨U', P.r + 1, P.e, fun z => P.p z + (if bf β z then (1 : F) else 0) • d, fun w z => if w = m then
                (if pass β then xor (P.c ib z) (bf β z && lin (P.s ib) d) else β)
              else xor (P.c w z) (bf β z && lin (P.s w) d), fun w => if w = m then (if pass β then P.s ib else 0) else P.s w⟩
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
      ⟨P.U, P.r, P.e, P.p, fun w => if w = m then (fun z => g.op.eval (g.inputs.map fun i => P.c i z)) else P.c w, fun w => if w = m then (g.inputs.map P.s).sum else P.s w⟩
    refine ⟨[Q], ?_, fun z x => ⟨fun h => cnt_single_mem Q z x h,
      fun h => cnt_single_not Q z x h⟩⟩
    intro Q' hQ'
    simp only [List.mem_singleton] at hQ'
    subst hQ'
    refine ⟨hrank, by simp only [Piece.U, Piece.r, Piece.e, Piece.p, Piece.c, Piece.s, Q]; rw [costG_snoc_zero _ _ hbin]; exact hcost,
      ⟨ds ++ [g'], hL', ?_, ?_, ?_⟩, ?_⟩
    · simp only [Piece.U, Piece.r, Piece.e, Piece.p, Piece.c, Piece.s, Q]
      rw [costG_snoc_zero _ _ (by rw [hg'op, hg'len]; simpa using hbin)]
      exact hdc
    · intro w hw
      rw [hlen1] at hw
      by_cases hwm : w = m
      · simp only [Piece.U, Piece.r, Piece.e, Piece.p, Piece.c, Piece.s, Q, hwm, if_true]
        exact real_congr hr' (fun z => by simp only [List.map_map]; rfl)
      · simp only [Piece.U, Piece.r, Piece.e, Piece.p, Piece.c, Piece.s, Q, hwm, if_false]
        exact real_mono _ (hcw w (by omega))
    · intro j; exact real_mono _ (hpb j)
    · intro z u hu w hw
      rw [hlen1] at hw
      by_cases hwm : w = m
      · subst hwm
        simp only [Piece.U, Piece.r, Piece.e, Piece.p, Piece.c, Piece.s, Q, if_true]
        rw [Cnew]
        have e1 : (g.inputs.map fun i => (gs.foldl step (bitsN k (P.p z + u) ++ bitsN t z)).getD i false)
            = g.inputs.map fun i => xor (P.c i z) (lin (P.s i) u) :=
          List.map_congr_left (fun i hi => hval z u hu i (hin i hi))
        rw [e1, aff_eval g.op g.inputs hg hbin (fun i => P.c i z) (fun i => lin (P.s i) u), lin_sum]
      · simp only [Piece.U, Piece.r, Piece.e, Piece.p, Piece.c, Piece.s, Q, hwm, if_false]
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


def pairMap {k : ℕ} (U : Submodule F (Fin k → F)) : (Fin k → F) →ₗ[F] (U →ₗ[F] F) :=
  { toFun := fun w =>
      { toFun := fun u => dotProduct w u.val
        map_add' := fun a b => dotProduct_add w a.val b.val
        map_smul' := fun c a => by simp [dotProduct_smul] }
    map_add' := fun a b => by ext u; exact add_dotProduct a b u.val
    map_smul' := fun c a => by ext u; simp [smul_dotProduct] }

def orthComp {k : ℕ} (U : Submodule F (Fin k → F)) : Submodule F (Fin k → F) :=
  LinearMap.ker (pairMap U)

lemma mem_orthComp {k : ℕ} (U : Submodule F (Fin k → F)) (w : Fin k → F) :
    w ∈ orthComp U ↔ ∀ u ∈ U, dotProduct w u = 0 := by
  simp only [orthComp, LinearMap.mem_ker, pairMap, LinearMap.ext_iff, LinearMap.coe_mk,
    AddHom.coe_mk, LinearMap.zero_apply, Subtype.forall]

lemma pairMap_surjective {k : ℕ} (U : Submodule F (Fin k → F)) :
    Function.Surjective (pairMap U) := by
  intro φ
  rcases Submodule.exists_isCompl U with ⟨V, hUV⟩
  let φ' : (Fin k → F) →ₗ[F] F := φ.comp (Submodule.projectionOnto U V hUV)
  let w : Fin k → F := fun j => φ' (Pi.single j 1)
  refine ⟨w, ?_⟩
  ext u
  have hu : u.val = ∑ j : Fin k, u.val j • Pi.single j (1 : F) := by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  have h1 : φ' u.val = φ u := by
    simp only [φ', LinearMap.comp_apply]
    rw [Submodule.projectionOnto_apply_left hUV u]
  rw [← h1]
  conv_rhs => rw [hu]
  rw [map_sum]
  simp only [pairMap, LinearMap.coe_mk, AddHom.coe_mk, dotProduct, map_smul, smul_eq_mul, w]
  apply Finset.sum_congr rfl
  intro j _; exact mul_comm _ _

lemma finrank_orthComp {k : ℕ} (U : Submodule F (Fin k → F)) :
    Module.finrank F (orthComp U) + Module.finrank F U = k := by
  have hrk := LinearMap.finrank_range_add_finrank_ker (pairMap U)
  have hran : LinearMap.range (pairMap U) = ⊤ := LinearMap.range_eq_top.mpr (pairMap_surjective U)
  rw [hran, finrank_top] at hrk
  have hdual : Module.finrank F (U →ₗ[F] F) = Module.finrank F U :=
    Subspace.dual_finrank_eq
  have htop : Module.finrank F (Fin k → F) = k := by simp
  rw [hdual, htop] at hrk
  change Module.finrank F U + Module.finrank F (orthComp U) = k at hrk
  omega

lemma card_submodule_eq_pow {k : ℕ} (U : Submodule F (Fin k → F)) [Fintype U] :
    Fintype.card U = 2 ^ Module.finrank F U := by
  let b := Module.finBasis F U
  have heq : U ≃ (Fin (Module.finrank F U) → F) := b.equivFun.toEquiv
  rw [Fintype.card_congr heq, Fintype.card_fun, Fintype.card_fin, ZMod.card]


open scoped Classical

abbrev V (n : ℕ) := Fin n → F

def sc (a b : Bool) : ℚ := if a = b then 1 else -1

theorem sc_le (a b : Bool) : sc a b ≤ 1 := by cases a <;> cases b <;> decide

theorem sc_flip (a b : Bool) : sc a (xor b true) = -sc a b := by cases a <;> cases b <;> decide

theorem piece_bound {n q g : ℕ} (U : Submodule F (V n)) [Fintype U]
    (hr : n ≤ Module.finrank F U + g) (p : V n) (s : Fin q → V n)
    (msg : U → Fin q → Bool) (read : (Fin q → Bool) → V n → Bool)
    (hi : ∀ u d : U, (∀ j, dotProduct (s j) d.val = 0) → msg (u+d) = msg u) :
    (∑ y : V n, ∑ u : U, sc (read (msg u) y) (lin y (p+u.val))) ≤
      (Fintype.card U : ℚ) * 2^(q+g) := by
  classical
  let A : U →ₗ[F] (Fin q → F) := {
    toFun := fun u j => dotProduct (s j) u.val
    map_add' := fun u v => by funext j; exact dotProduct_add _ _ _
    map_smul' := fun a u => by ext j; simp [dotProduct_smul] }
  let B := (LinearMap.ker A).map U.subtype
  have hB : Module.finrank F B = Module.finrank F (LinearMap.ker A) := Submodule.finrank_map_subtype_eq _ _
  have hd : Module.finrank F (orthComp B) ≤ q+g := by
    have hh := finrank_orthComp B
    have hk := LinearMap.finrank_range_add_finrank_ker A
    have hah : Module.finrank F (LinearMap.range A) ≤ q := by
      simpa using (LinearMap.range A).finrank_le
    rw [hB] at hh
    omega
  let v := fun (y : V n) (u : U) => sc (read (msg u) y) (lin y (p+u.val))
  have hc (y : V n) (hy : y ∉ orthComp B) : ∑ u : U, v y u = 0 := by
    rw [mem_orthComp] at hy
    push Not at hy
    obtain ⟨d,hd,hz⟩ := hy
    obtain ⟨d,hker,rfl⟩ := hd
    have hz1 : dotProduct y d.val = 1 := by
      rcases (show ∀ z : F, z = 0 ∨ z = 1 by decide) (dotProduct y d.val) with h | h
      · exact (hz h).elim
      · exact h
    have hm : ∀ j, dotProduct (s j) d.val = 0 := fun j => congrFun (LinearMap.mem_ker.mp hker) j
    have hv (u : U) : v y (u+d) = -v y u := by
      dsimp only [v]
      rw [hi u d hm]
      change sc _ (lin y (p + (u.val+d.val))) = _
      rw [← add_assoc, lin_add_right]
      have hb : lin y d.val = true := by simp [lin,hz1]
      rw [hb, sc_flip]
    have he : (∑ u : U, v y (u+d)) = ∑ u : U, v y u :=
      Fintype.sum_equiv (Equiv.addRight d) _ _ (fun u => rfl)
    simp_rw [hv, Finset.sum_neg_distrib] at he
    linarith
  change (∑ y : V n, ∑ u : U, v y u) ≤ _
  calc
    _ ≤ ∑ y : V n, if y ∈ orthComp B then (Fintype.card U : ℚ) else 0 := by
      apply Finset.sum_le_sum
      intro y _
      by_cases hy : y ∈ orthComp B
      · simp only [hy, ite_true]
        calc
          _ ≤ ∑ _u : U, (1:ℚ) := Finset.sum_le_sum (fun u _ => sc_le _ _)
          _ = _ := by simp
      · simp [hy, hc y hy]
    _ = (Fintype.card (orthComp B) : ℚ) * (Fintype.card U : ℚ) := by
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, Fintype.card_subtype (fun a : V n => a ∈ orthComp B)]
    _ ≤ _ := by
      rw [card_submodule_eq_pow, mul_comm]
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      push_cast
      exact pow_le_pow_right₀ (by norm_num) hd


theorem cardV (n : ℕ) : Fintype.card (V n) = 2^n := by simp [V,F,Fintype.card_fun]

def sendT {n q : ℕ} (C : Circuit) (tap : Fin q → ℕ) (x : V n) (j : Fin q) : Bool :=
  (C.wires (bitsN n x)).getD (tap j) false

theorem circuit_bound {n q g : ℕ} (C : Circuit) (tap : Fin q → ℕ)
    (read : (Fin q → Bool) → V n → Bool)
    (hback : ∀ i : Fin C.gates.length, ∀ v ∈ (C.gates.get i).inputs, v < n+i.val)
    (hop : ∀ G ∈ C.gates, GOk G) (hcost : costG C.gates ≤ g)
    (htap : ∀ j, tap j < n+C.gates.length) :
    (∑ y : V n, ∑ x : V n, sc (read (sendT C tap x) y) (lin y x)) ≤
      (2:ℚ)^n * 2^(q+g) := by
  classical
  obtain ⟨L,hL,hcnt⟩ := all_gates (k:=n) (t:=0) C hop (by
    intro j hj v hv
    apply hback ⟨j,hj⟩ v
    simpa [List.getD_eq_getElem?_getD,hj,List.get_eq_getElem] using hv) C.gates.length le_rfl
  rw [List.take_length] at hL
  let P := fun i : Fin L.length => L.get i
  let U := fun i : Fin L.length => (P i).U
  let p := fun i : Fin L.length => (P i).p 0
  let f : (Σ i, U i) → V n := fun a => p a.1 + a.2.val
  have hu (x : V n) : ∃! i : Fin L.length, x - p i ∈ U i :=
    exists_unique_of_count (fun Q : Piece n 0 => x - Q.p 0 ∈ Q.U) L (hcnt 0 x)
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨i,u⟩ ⟨j,v⟩ he
      change p i + u.val = p j + v.val at he
      have h1 : p i + u.val - p i ∈ U i := by simpa using u.property
      have h2 : p i + u.val - p j ∈ U j := by rw [he]; simpa using v.property
      have hij := (hu (p i + u.val)).unique h1 h2
      subst j
      have huv : u = v := Subtype.ext (add_left_cancel he)
      subst v; rfl
    · intro x
      obtain ⟨i,hi,_⟩ := hu x
      exact ⟨⟨i,⟨x-p i,hi⟩⟩, by dsimp [f]; abel⟩
  let e := Equiv.ofBijective f hf
  have hs (F0 : V n → ℚ) : (∑ x, F0 x) = ∑ i, ∑ u : U i, F0 (p i + u.val) := by
    rw [← e.sum_comp F0, Fintype.sum_sigma]
    rfl
  have hcard : (∑ i, (Fintype.card (U i) : ℚ)) = (2:ℚ)^n := by
    simpa [cardV] using (hs (fun _ => 1)).symm
  let score := fun (y x : V n) => sc (read (sendT C tap x) y) (lin y x)
  change (∑ y, ∑ x, score y x) ≤ _
  calc
    _ = ∑ i, ∑ y, ∑ u : U i, score y (p i + u.val) := by
      trans ∑ y, ∑ i, ∑ u : U i, score y (p i + u.val)
      · exact Finset.sum_congr rfl (fun y _ => hs (score y))
      · exact Finset.sum_comm
    _ ≤ ∑ i, (Fintype.card (U i) : ℚ) * 2^(q+g) := by
      apply Finset.sum_le_sum
      intro i _
      have hP := hL (P i) (List.get_mem L i)
      obtain ⟨hr,he,_,hwire⟩ := hP
      have hrank : n ≤ Module.finrank F (U i) + g := by change n ≤ Module.finrank F (P i).U + g; omega
      let s := fun j => (P i).s (tap j)
      let msg := fun u : U i => sendT C tap (p i+u.val)
      have hm (u : U i) (j : Fin q) : msg u j = xor ((P i).c (tap j) 0) (lin (s j) u.val) := by
        have hv := hwire 0 u.val u.property (tap j) (by simpa using htap j)
        change (C.gates.foldl step (bitsN n (p i + u.val))).getD (tap j) false = _
        simpa only [bitsN,List.ofFn_zero,List.append_nil,p,s] using hv
      apply piece_bound (U i) hrank (p i) s msg read
      intro u d hd
      funext j
      rw [hm,hm]
      change xor _ (lin (s j) (u.val+d.val)) = _
      rw [lin_add_right]
      have hb : lin (s j) d.val = false := by simp [lin,hd j]
      simp [hb]
    _ = _ := by rw [← Finset.sum_mul, hcard]


def Universal (n h g : Nat) : Prop :=
  let W := Fin n → Bool
  let H := 2^h
  let Circ := PEqualNP.CircuitLowerBounds.Circuit
  let legal := fun (C : Circ) =>
    (∀ i : Fin C.gates.length, ∀ v ∈ (C.gates.get i).inputs, v < n+i.val) ∧
    (∀ opGate ∈ C.gates, opGate.inputs.length ≤ 2 ∧
      (opGate.op = .and ∨ opGate.op = .or ∨ opGate.op = .mod 2 ∨
        (opGate.op = .not ∧ opGate.inputs.length = 1)))
  let cost := fun (C : Circ) => C.gates.countP (fun gate => @decide
    ((gate.op = .and ∨ gate.op = .or) ∧ gate.inputs.length = 2) (Classical.propDecidable _))
  let universal := fun (g : Nat) =>
    ∀ (k : Nat) (truth : W → Fin k → Bool) (w : W → Fin k → ℚ) (D : Fin k → Finset W),
      (∀ x y, 0 ≤ w x y) → (∀ y, 16*(∑ x : W, (w x y)^2) ≤ (H : ℚ)) →
      ∃ (z : Nat) (C : Fin z → Circ) (tap : Fin z → Fin (h+1) → Nat)
        (read : Fin z → (Fin (h+1) → Bool) → Fin k → Bool),
        0 < z ∧ (∀ s, legal (C s) ∧ cost (C s) ≤ g ∧ ∀ j, tap s j < n+(C s).gates.length) ∧
        ∀ x y,
          let reward : ℚ := if x ∈ D y then 1 else min (w x y) (1/2)
          let hits := ((Finset.univ : Finset (Fin z)).filter (fun s =>
            read s (fun j => ((C s).wires (List.ofFn x)).getD (tap s j) false) y = truth x y)).card
          (1+reward-2*((D y).card : ℚ)/(H : ℚ))*(z : ℚ) ≤ 2*(hits : ℚ)
  universal g

theorem direct_budget {n h g : Nat} (hn : n ≤ h+1) : Universal n h g := by
  classical
  intro k truth w D hw hmass
  let C : Circuit := ⟨[⟨.or, []⟩], 0⟩
  let tap : Fin (h+1) → Nat := fun j => min j.val n
  let idx : Fin n → Fin (h+1) := fun i => ⟨i.val, lt_of_lt_of_le i.isLt hn⟩
  refine ⟨1, fun _ => C, fun _ => tap, fun _ msg y => truth (fun i => msg (idx i)) y, by decide, ?_, ?_⟩
  · intro s
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · intro i v hv
      simp [C, List.get_eq_getElem] at hv
    · intro G hG
      simp [C] at hG
      subst G
      simp
    · simp [C]
    · intro j
      dsimp [tap,C]
      have := min_le_right j.val n
      omega
  · intro x y
    have hb (i : Fin n) : (C.wires (List.ofFn x)).getD (tap (idx i)) false = x i := by
      simp [tap, idx, Nat.min_eq_left (Nat.le_of_lt i.isLt), C, Circuit.wires,
        List.getD_eq_getElem?_getD, i.isLt, List.getElem?_append]
    have hre : (fun i : Fin n => (C.wires (List.ofFn x)).getD (tap (idx i)) false) = x := funext hb
    simp only [hre]
    simp
    have hn0 : 0 ≤ (2 * ((D y).card : ℚ)) / (2 : ℚ)^h := by positivity
    by_cases hm : x ∈ D y
    · simp only [if_pos hm]; linarith
    · simp only [if_neg hm]; linarith [min_le_right (w x y) (1/2 : ℚ)]


def boolEquiv (n : ℕ) : V n ≃ (Fin n → Bool) where
  toFun x j := decide (x j = 1)
  invFun x j := if x j then 1 else 0
  left_inv x := by
    funext j
    have hb : ∀ a : F, (if decide (a=1) then (1:F) else 0) = a := by decide
    exact hb (x j)
  right_inv x := by funext j; cases h : x j <;> simp [h]

theorem sum_sc {z : ℕ} (p : Fin z → Bool) (b : Bool) :
    ∑ i, sc (p i) b = 2*(((Finset.univ : Finset (Fin z)).filter (fun i => p i = b)).card : ℚ) - z := by
  classical
  have hw (i : Fin z) : sc (p i) b = 2*(if p i = b then (1:ℚ) else 0)-1 := by
    unfold sc; split <;> norm_num
  simp_rw [hw]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_filter]
  simp

theorem converse {n h g : ℕ} (hh : h ≤ n) (hu : Universal n h g) : (n-h)/2 ≤ g+3 := by
  classical
  let d := (n-h+1)/2
  let δ : ℚ := 1 / (4 * (2:ℚ)^d)
  have hdpos : (0:ℚ) < 4*2^d := by positivity
  have hdhalf : δ ≤ 1/2 := by
    apply (div_le_iff₀ hdpos).2
    have h1 : (1:ℚ) ≤ 2^d := one_le_pow₀ (by norm_num)
    linarith
  have hn : n ≤ h + d*2 := by dsimp [d]; omega
  have hp : (2:ℚ)^n ≤ 2^h * (2^d)^2 := by
    rw [← pow_mul, ← pow_add]
    exact pow_le_pow_right₀ (by norm_num) hn
  have hm : 16 * (∑ _x : Fin n → Bool, δ^2) ≤ (2:ℚ)^h := by
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fun,Fintype.card_bool,
      Fintype.card_fin,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
    dsimp only [δ]
    field_simp
    nlinarith [hp]
  let Y := Fintype.equivFin (V n)
  let truth := fun (x : Fin n → Bool) (j : Fin (Fintype.card (V n))) =>
    lin (Y.symm j) ((boolEquiv n).symm x)
  obtain ⟨z,C,tap,read,hz,hlegal,hpred⟩ := hu (Fintype.card (V n)) truth (fun _ _ => δ)
    (fun _ => ∅) (by intros; dsimp [δ]; positivity) (fun _ => by simpa using hm)
  let A := fun (s : Fin z) (y x : V n) => sc (read s (sendT (C s) (tap s) x) (Y y)) (lin y x)
  have hx (y x : V n) : δ * (z : ℚ) ≤ ∑ s, A s y x := by
    let pr := fun s : Fin z => read s (sendT (C s) (tap s) x) (Y y)
    change δ * (z : ℚ) ≤ ∑ s, sc (pr s) (lin y x)
    rw [sum_sc]
    have hp0 := hpred ((boolEquiv n) x) (Y y)
    have he : truth ((boolEquiv n) x) (Y y) = lin y x := by simp [truth]
    simp only [he,Finset.notMem_empty,ite_false,min_eq_left hdhalf,Finset.card_empty,Nat.cast_zero,
      mul_zero,zero_div,sub_zero] at hp0
    change (1+δ) * (z:ℚ) ≤ 2 * (((Finset.univ : Finset (Fin z)).filter (fun s => pr s = lin y x)).card : ℚ) at hp0
    linarith
  have hs (s : Fin z) : (∑ y, ∑ x, A s y x) ≤ (2:ℚ)^n * 2^(h+1+g) := by
    obtain ⟨⟨hb,ho⟩,hc,ht⟩ := hlegal s
    exact circuit_bound (C s) (tap s) (fun msg y => read s msg (Y y)) hb ho hc ht
  have htot : (2:ℚ)^n * (2^n * (δ*z)) ≤ (z:ℚ) * (2^n * 2^(h+1+g)) := by
    calc
      _ = ∑ _y : V n, ∑ _x : V n, δ * z := by simp [cardV]
      _ ≤ ∑ y, ∑ x, ∑ s, A s y x := Finset.sum_le_sum (fun y _ => Finset.sum_le_sum (fun x _ => hx y x))
      _ = ∑ s, ∑ y, ∑ x, A s y x := by
        trans ∑ y, ∑ s, ∑ x, A s y x
        · exact Finset.sum_congr rfl (fun y _ => Finset.sum_comm)
        · exact Finset.sum_comm
      _ ≤ ∑ _s : Fin z, (2:ℚ)^n * 2^(h+1+g) := Finset.sum_le_sum (fun s _ => hs s)
      _ = _ := by simp
  have hcancel : (2:ℚ)^n * δ ≤ 2^(h+1+g) := by
    have hf : ((z:ℚ)*2^n)*(2^n*δ) ≤ ((z:ℚ)*2^n)*2^(h+1+g) := by calc
      _ = (2:ℚ)^n * (2^n * (δ*z)) := by ring
      _ ≤ _ := htot
      _ = _ := by ring
    exact le_of_mul_le_mul_left hf (by positivity)
  dsimp only [δ] at hcancel
  rw [mul_one_div] at hcancel
  have hp2 := (div_le_iff₀ hdpos).mp hcancel
  have he : (2:ℚ)^n ≤ 2^(h+1+g+d+2) := by
    calc
      _ ≤ _ := hp2
      _ = _ := by rw [pow_add (_ : ℚ) (h+1+g+d) 2,pow_add (_ : ℚ) (h+1+g) d]; ring
  have hh2 := (pow_le_pow_iff_right₀ (show (1:ℚ) < 2 by norm_num)).mp he
  dsimp [d] at hh2
  omega


theorem sqF (a : F) : a*a = a := by revert a; decide

theorem eitherF (a : F) : a = 0 ∨ a = 1 := by revert a; decide

theorem quadratic_factors (N : ℕ) : ∀ (E : Type) [AddCommGroup E] [Module F E] [FiniteDimensional F E],
    Module.finrank F E = N → ∀ Q : QuadraticForm F E,
    ∃ (r : ℕ) (l : E →ₗ[F] F) (a b : Fin r → (E →ₗ[F] F)),
      r ≤ N/2 ∧ ∀ x, Q x = l x + ∑ j, a j x * b j x := by
  classical
  induction N using Nat.strong_induction_on with
  | ind N ih =>
    intro E _ _ _ hN Q
    have addp (v w : E) : Q (v+w) = Q v + Q w + Q.polarBilin v w := QuadraticMap.map_add Q v w
    by_cases h : ∀ v w, Q.polarBilin v w = 0
    · let l : E →ₗ[F] F := {
        toFun := Q
        map_add' := fun x y => by rw [addp,h,add_zero]
        map_smul' := fun a x => by rw [Q.map_smul,sqF]; rfl }
      exact ⟨0,l,Fin.elim0,Fin.elim0,Nat.zero_le _,fun x => by simp [l]⟩
    push Not at h
    obtain ⟨v,w,hn⟩ := h
    have hvw : Q.polarBilin v w = 1 := (eitherF _).resolve_left hn
    have hwv : Q.polarBilin w v = 1 := (QuadraticMap.polar_comm Q w v).trans hvw
    have self (x : E) : Q.polarBilin x x = 0 := by
      change QuadraticMap.polar Q x x = 0
      rw [Q.polar_self]
      exact (show ∀ z : F, 2 • z = 0 by decide) (Q x)
    let A := Q.polarBilin v
    let B := Q.polarBilin w
    have Av : A v = 0 := self v
    have Aw : A w = 1 := hvw
    have Bv : B v = 1 := hwv
    have Bw : B w = 0 := self w
    let T := A.prod B
    let K := LinearMap.ker T
    have sur : Function.Surjective T := by
      rintro ⟨a,b⟩
      refine ⟨a • w + b • v, Prod.ext ?_ ?_⟩ <;> simp [T,Av,Aw,Bv,Bw]
    have dim : 2 + Module.finrank F K = N := by
      have hh := LinearMap.finrank_range_add_finrank_ker T
      rw [LinearMap.range_eq_top.mpr sur,finrank_top,hN] at hh
      simpa [K,Module.finrank_prod] using hh
    let R0 : E →ₗ[F] E := LinearMap.id - A.smulRight w - B.smulRight v
    have Rmem (x : E) : R0 x ∈ K := by
      apply LinearMap.mem_ker.mpr
      apply Prod.ext <;> simp [R0,T,Av,Aw,Bv,Bw]
    let R := R0.codRestrict K Rmem
    have decomp (x : E) : (R x : E) + A x • w + B x • v = x := by
      change x - A x • w - B x • v + A x • w + B x • v = x
      abel
    have qval (u : K) (a b : F) : Q (u.val + a • w + b • v) =
        Q u.val + a * Q w + b * Q v + a*b := by
      have ha : A u.val = 0 := congrArg Prod.fst (LinearMap.mem_ker.mp u.property)
      have hb : B u.val = 0 := congrArg Prod.snd (LinearMap.mem_ker.mp u.property)
      have huv : Q.polarBilin u.val v = 0 := (QuadraticMap.polar_comm Q _ _).trans ha
      have huw : Q.polarBilin u.val w = 0 := (QuadraticMap.polar_comm Q _ _).trans hb
      rcases eitherF a with rfl | rfl <;> rcases eitherF b with rfl | rfl <;>
        simp [addp,huv,huw,hwv,LinearMap.add_apply,add_assoc] <;>
        change Q.polarBilin u.val w + Q.polarBilin u.val v = 0 <;> rw [huw,huv,add_zero]
    obtain ⟨r,l,aa,bb,hr,hq⟩ := ih (Module.finrank F K) (by omega) K rfl (Q.comp K.subtype)
    refine ⟨r+1,l.comp R + (Q w) • A + (Q v) • B,
      Fin.cons A (fun j => (aa j).comp R), Fin.cons B (fun j => (bb j).comp R), by omega, ?_⟩
    intro x
    have hh := qval (R x) (A x) (B x)
    rw [decomp] at hh
    have hk : Q (R x : E) = l (R x) + ∑ j, aa j (R x) * bb j (R x) := hq (R x)
    rw [hh,hk,Fin.sum_univ_succ]
    simp only [LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul,LinearMap.comp_apply,Fin.cons_zero,Fin.cons_succ]
    ring


def toField : Bool ≃ ZMod 2 where
  toFun b := if b then 1 else 0
  invFun z := z == 1
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def paid (g : Gate) : Prop :=
  (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2

noncomputable def paidBool (g : Gate) : Bool := @decide (paid g) (Classical.propDecidable _)

noncomputable def paidCount (gs : List Gate) : ℕ := gs.countP paidBool

def legalOp (g : Gate) : Prop :=
  g.inputs.length ≤ 2 ∧
    (g.op = .and ∨ g.op = .or ∨ g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1))

def appendWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun n => w.getD n false)]
@[local simp] theorem field_false : toField false = 0 := by decide +kernel
section Build

def readsBack (n : ℕ) (gs : List Gate) : Prop :=
  ∀ i : Fin gs.length, ∀ w ∈ (gs.get i).inputs, w < n+i.val

abbrev Plan (n : ℕ) :=
  {gs : List Gate // readsBack n gs ∧ ∀ g ∈ gs, legalOp g}

namespace Plan

abbrev gates {n : ℕ} (P : Plan n) : List Gate := P.val

theorem back {n : ℕ} (P : Plan n) : readsBack n P.gates := P.property.1

theorem legal {n : ℕ} (P : Plan n) : ∀ g ∈ P.gates, legalOp g := P.property.2

end Plan

def emptyPlan (n : ℕ) : Plan n := ⟨[], ⟨by simp [readsBack], by simp⟩⟩

def Evaluates {X : Type} {n : ℕ} (input : X → List Bool) (P : Plan n)
    (f : X → Bool) : Prop :=
  ∃ i, i < n+P.gates.length ∧ ∀ x, (P.gates.foldl appendWire (input x)).getD i false = f x

def adds {n : ℕ} (P D : Plan n) (k : ℕ) : Prop :=
  (∃ rest, D.gates = P.gates ++ rest) ∧ paidCount D.gates ≤ paidCount P.gates + k

theorem adds_refl {n : ℕ} (P : Plan n) : adds P P 0 :=
  ⟨⟨[],by simp⟩,by simp⟩

theorem adds_trans {n k l : ℕ} {P D E : Plan n} (h : adds P D k) (j : adds D E l) :
    adds P E (k+l) := by
  obtain ⟨⟨v,hv⟩,hk⟩ := h
  obtain ⟨⟨w,hw⟩,hl⟩ := j
  exact ⟨⟨v++w,by rw [hw,hv,List.append_assoc]⟩,by omega⟩

theorem adds_mono {n k l : ℕ} {P D : Plan n} (h : adds P D k) (le : k ≤ l) :
    adds P D l :=
  ⟨h.1,h.2.trans (Nat.add_le_add_left le _)⟩

theorem appendWire_length (gs : List Gate) (v : List Bool) :
    (gs.foldl appendWire v).length = v.length + gs.length := by
  induction gs generalizing v with
  | nil => simp
  | cons g gs ih => simp [ih, appendWire]; omega

theorem appendWire_prefix (gs : List Gate) (v : List Bool) :
    ∃ w, gs.foldl appendWire v = v ++ w := by
  induction gs generalizing v with
  | nil => exact ⟨[],by simp⟩
  | cons g gs ih =>
    obtain ⟨w,hw⟩ := ih (appendWire v g)
    refine ⟨[g.op.eval (g.inputs.map fun i => v.getD i false)] ++ w,?_⟩
    rw [List.foldl_cons, hw]
    simp [appendWire]

theorem getD_prefix (v w : List Bool) {i : ℕ} (hi : i < v.length) :
    (v++w).getD i false = v.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem evaluates_ext {X : Type} {n k : ℕ} {input : X → List Bool}
    (size : ∀ x, (input x).length = n) {P D : Plan n} {f : X → Bool}
    (h : Evaluates input P f) (extend : adds P D k) : Evaluates input D f := by
  obtain ⟨i,hi,hf⟩ := h
  obtain ⟨rest,hr⟩ := extend.1
  refine ⟨i,by rw [hr,List.length_append]; omega,?_⟩
  intro x
  rw [hr,List.foldl_append]
  obtain ⟨w,hw⟩ := appendWire_prefix rest (P.gates.foldl appendWire (input x))
  rw [hw, getD_prefix _ _ (by simpa [appendWire_length,size] using hi)]
  exact hf x

def planGate {n : ℕ} (P : Plan n) (g : Gate)
    (hprev : ∀ w ∈ g.inputs, w < n+P.gates.length) (hlegal : legalOp g) : Plan n := by
  refine ⟨P.gates ++ [g], ?_, ?_⟩
  ·
    intro i w hw
    by_cases h : i.val < P.gates.length
    · have eq : (P.gates ++ [g]).get i = P.gates.get ⟨i.val,h⟩ := by
        simp [List.get_eq_getElem, List.getElem_append_left h]
      rw [eq] at hw
      exact P.back ⟨i.val,h⟩ w hw
    · have hi : i.val = P.gates.length := by
        have := i.isLt
        simp at this
        omega
      have eq : (P.gates ++ [g]).get i = g := by
        simp [List.get_eq_getElem, hi]
      rw [eq] at hw
      simpa [hi] using hprev w hw
  · intro h hh
    rcases List.mem_append.mp hh with old | new
    · exact P.legal h old
    · have : h = g := by simpa using new
      simpa [this] using hlegal

theorem emit_gate {X : Type} {n : ℕ} {input : X → List Bool}
    (size : ∀ x, (input x).length = n) (P : Plan n) (op : GateOp) (w : List ℕ)
    (old : ∀ i ∈ w, i < n + P.gates.length) (legal : legalOp ⟨op,w⟩) :
    ∃ D, adds P D (paidCount [⟨op,w⟩]) ∧ Evaluates input D
      (fun x => op.eval (w.map fun i => (P.gates.foldl appendWire (input x)).getD i false)) := by
  let g : Gate := ⟨op,w⟩
  let D := planGate P g old legal
  refine ⟨D,⟨⟨[g],rfl⟩,?_⟩,n+P.gates.length,?_,?_⟩
  · simp [D,planGate,Plan.gates,paidCount,List.countP_append,g]
  · simp [D,planGate,Plan.gates]
  · intro x
    have index := appendWire_length P.gates (input x)
    rw [size] at index
    change ((P.gates ++ [g]).foldl appendWire (input x)).getD (n+P.gates.length) false = _
    rw [List.foldl_append]
    simp [appendWire, g, ← index, List.getD_eq_getElem?_getD]

theorem emit_const {X : Type} {n : ℕ} {input : X → List Bool}
    (size : ∀ x, (input x).length = n) (P : Plan n) (b : Bool) :
    ∃ D, adds P D 0 ∧ Evaluates input D (fun _ => b) := by
  cases b
  · simpa [paidCount,paidBool,paid,GateOp.eval] using
      emit_gate size P .or [] (by simp) ⟨by simp,Or.inr (Or.inl rfl)⟩
  · simpa [paidCount,paidBool,paid,GateOp.eval] using
      emit_gate size P .and [] (by simp) ⟨by simp,Or.inl rfl⟩

theorem emit_not {X : Type} {n : ℕ} {input : X → List Bool}
    (size : ∀ x, (input x).length = n) (P : Plan n)
    {f : X → Bool} (hf : Evaluates input P f) :
    ∃ D, adds P D 0 ∧ Evaluates input D (fun x => !(f x)) := by
  obtain ⟨i,hi,hfi⟩ := hf
  obtain ⟨D,hd,out⟩ := emit_gate size P .not [i] (by simpa using hi)
    ⟨by simp,Or.inr (Or.inr (Or.inr ⟨rfl,rfl⟩))⟩
  refine ⟨D,?_,?_⟩
  · simpa [paidCount,paidBool,paid] using hd
  · simpa [GateOp.eval,-List.getD_eq_getElem?_getD,hfi] using out

theorem emit_and {X : Type} {n : ℕ} {input : X → List Bool}
    (size : ∀ x, (input x).length = n) (P : Plan n)
    {f g : X → Bool} (hf : Evaluates input P f) (hg : Evaluates input P g) :
    ∃ D, adds P D 1 ∧ Evaluates input D (fun x => f x && g x) := by
  obtain ⟨i,hi,hfi⟩ := hf
  obtain ⟨j,hj,hgj⟩ := hg
  have refs : ∀ w ∈ [i,j], w < n + P.gates.length := by
    simp_all
  obtain ⟨D,hd,out⟩ := emit_gate size P .and [i,j] refs ⟨by simp,Or.inl rfl⟩
  refine ⟨D,?_,?_⟩
  · simpa [paidCount,paidBool,paid] using hd
  · simpa [GateOp.eval,-List.getD_eq_getElem?_getD,hfi,hgj] using out

theorem emit_xor {X : Type} {n : ℕ} {input : X → List Bool}
    (size : ∀ x, (input x).length = n) (P : Plan n)
    {f g : X → Bool} (hf : Evaluates input P f) (hg : Evaluates input P g) :
    ∃ D, adds P D 0 ∧ Evaluates input D (fun x => Bool.xor (f x) (g x)) := by
  obtain ⟨i,hi,hfi⟩ := hf
  obtain ⟨j,hj,hgj⟩ := hg
  have refs : ∀ w ∈ [i,j], w < n + P.gates.length := by
    simp_all
  obtain ⟨D,hd,out⟩ := emit_gate size P (.mod 2) [i,j] refs ⟨by simp,Or.inr (Or.inr (Or.inl rfl))⟩
  have cost : adds P D 0 := by simpa [paidCount,paidBool,paid] using hd
  obtain ⟨E,he,result⟩ := emit_not size D out
  have eq (x : X) :
      (!(GateOp.eval (.mod 2) [(P.gates.foldl appendWire (input x)).getD i false,
        (P.gates.foldl appendWire (input x)).getD j false])) = Bool.xor (f x) (g x) := by
    rw [hfi,hgj]
    cases f x <;> cases g x <;> rfl
  refine ⟨E,by simpa using adds_trans cost he,?_⟩
  change Evaluates input E (fun x => !(GateOp.eval (.mod 2)
    [(P.gates.foldl appendWire (input x)).getD i false,
      (P.gates.foldl appendWire (input x)).getD j false])) at result
  rw [funext eq] at result
  exact result

theorem build_many {X I J : Type} {n : ℕ} {input : X → List Bool}
    (size : ∀ x, (input x).length = n) (P : Plan n) (k : ℕ)
    (s : Finset I) (f : I → J → X → Bool)
    (each : ∀ i ∈ s, ∀ (D : Plan n) (v : ℕ), adds P D v →
      ∃ E, adds D E k ∧ ∀ j, Evaluates input E (f i j)) :
    ∃ D, adds P D (s.card*k) ∧ ∀ i ∈ s, ∀ j, Evaluates input D (f i j) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨P,by simpa using adds_refl P,by simp⟩
  | @insert i s hi ih =>
    obtain ⟨D,extend,results⟩ := ih (fun j hj => each j (Finset.mem_insert_of_mem hj))
    obtain ⟨E,next,new⟩ := each i (Finset.mem_insert_self _ _) D _ extend
    refine ⟨E,by simpa [Finset.card_insert_of_notMem hi,Nat.add_mul] using adds_trans extend next,?_⟩
    intro j hj p
    rcases Finset.mem_insert.mp hj with eq | old
    · simpa [eq] using new p
    · exact evaluates_ext size (results j old p) next

end Build
open scoped BigOperators

section Synthesis

variable {X : Type} {n : ℕ} {input : X → List Bool}
variable (size : ∀ x, (input x).length = n)

theorem field_xor (a b : Bool) : toField (Bool.xor a b) = toField a + toField b := by
  cases a <;> cases b <;> decide +kernel

include size in
theorem emit_sum {I : Type} (P : Plan n) (S : Finset I) (f : I → X → Bool)
    (h : ∀ i ∈ S, Evaluates input P (f i)) :
    ∃ D, adds P D 0 ∧ Evaluates input D (fun x => toField.symm (∑ i ∈ S, toField (f i x))) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simpa [← field_false] using emit_const size P false
  | @insert i S hi ih =>
    obtain ⟨D,hd,prev⟩ := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    have current := evaluates_ext size (h i (Finset.mem_insert_self _ _)) hd
    obtain ⟨E,he,sum⟩ := emit_xor size D current prev
    refine ⟨E,by simpa using adds_trans hd he,?_⟩
    have eq (x : X) :
        Bool.xor (f i x) (toField.symm (∑ j ∈ S, toField (f j x))) =
          toField.symm (∑ j ∈ insert i S, toField (f j x)) := by
      apply toField.injective
      simp [field_xor, Finset.sum_insert hi]
    simpa only [funext eq] using sum

include size in
theorem build_values {I : Type} (P : Plan n) (k : ℕ)
    (S : Finset I) (f : I → X → Bool)
    (each : ∀ i ∈ S, ∀ (D : Plan n) (v : ℕ), adds P D v →
      ∃ E, adds D E k ∧ Evaluates input E (f i)) :
    ∃ D, adds P D (S.card*k) ∧ ∀ i ∈ S, Evaluates input D (f i) := by
  obtain ⟨D,hd,h⟩ := build_many size P k S (fun i (_ : Unit) => f i) (by
    intro i hi D v hd
    obtain ⟨E,he,eval⟩ := each i hi D v hd
    exact ⟨E,he,fun _ => eval⟩)
  exact ⟨D,hd,fun i hi => h i hi ()⟩

end Synthesis

abbrev evF {n : ℕ} (P : Plan n) (f : V n → F) := Evaluates (bitsN n) P (fun x => toField.symm (f x))

theorem evF_ext {n k : ℕ} {P D : Plan n} {f : V n → F} (h : evF P f) (hd : adds P D k) :
    evF D f := evaluates_ext (bitsN_length n) h hd

theorem emit_addF {n : ℕ} (P : Plan n) {f g : V n → F} (hf : evF P f) (hg : evF P g) :
    ∃ D, adds P D 0 ∧ evF D (fun x => f x + g x) := by
  obtain ⟨D,hd,he⟩ := emit_xor (bitsN_length n) P hf hg
  refine ⟨D,hd,?_⟩
  have h (x : V n) : xor (toField.symm (f x)) (toField.symm (g x)) = toField.symm (f x + g x) :=
    toField.injective (by simp [field_xor])
  simpa only [funext h] using he

theorem emit_mulF {n : ℕ} (P : Plan n) {f g : V n → F} (hf : evF P f) (hg : evF P g) :
    ∃ D, adds P D 1 ∧ evF D (fun x => f x * g x) := by
  obtain ⟨D,hd,he⟩ := emit_and (bitsN_length n) P hf hg
  refine ⟨D,hd,?_⟩
  have h (a b : F) : (toField.symm a && toField.symm b) = toField.symm (a*b) := by revert a b; decide
  simpa only [h] using he

theorem emit_linear {n : ℕ} (P : Plan n) (L : V n →ₗ[F] F) :
    ∃ D, adds P D 0 ∧ evF D L := by
  classical
  let S := (Finset.univ : Finset (Fin n)).filter (fun i => L (Pi.single i (1:F)) = 1)
  have he (x : V n) : L x = ∑ i ∈ S, x i := by
    have hx : x = ∑ i, x i • Pi.single i (1:F) := by ext j; simp [Finset.sum_apply,Pi.single_apply]
    calc
      _ = L (∑ i, x i • Pi.single i 1) := congrArg L hx
      _ = _ := by
        rw [map_sum,Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro i _
        rcases (show ∀ z : F, z = 0 ∨ z = 1 by decide) (L (Pi.single i 1)) with hh | hh <;> simp [hh]
  have hi (i : Fin n) : evF P (fun x => x i) := by
    refine ⟨i.val,by have := i.isLt; omega,?_⟩
    intro x
    change (P.gates.foldl step (bitsN n x)).getD i.val false = _
    rw [foldl_step_getD P.gates _ _ (by simpa [bitsN] using i.isLt),bitsN_getD _ _ _ i.isLt]
    exact (show ∀ a : F, decide (a=1) = toField.symm a by decide) (x i)
  obtain ⟨D,hd,hdv⟩ := emit_sum (bitsN_length n) P S (fun i x => toField.symm (x i)) (fun i _ => hi i)
  refine ⟨D,hd,?_⟩
  unfold evF
  simpa only [Equiv.apply_symm_apply,he] using hdv


theorem emit_linproduct {n : ℕ} (P : Plan n) (L M : V n →ₗ[F] F) :
    ∃ D, adds P D 1 ∧ evF D (fun x => L x * M x) := by
  obtain ⟨D,hD,hL⟩ := emit_linear P L
  obtain ⟨E,hE,hM⟩ := emit_linear D M
  obtain ⟨G,hG,hout⟩ := emit_mulF E (evF_ext hL hE) hM
  exact ⟨G,by simpa using adds_trans (adds_trans hD hE) hG,hout⟩

theorem compile_message {n h t : ℕ} (L : Fin h → (V n →ₗ[F] F)) (K : V n →ₗ[F] V t)
    (c : F) (ell : V t →ₗ[F] F) (Q : QuadraticForm F (V t)) :
    ∃ (C : Circuit) (tap : Fin (h+1) → ℕ),
      (∀ i : Fin C.gates.length, ∀ v ∈ (C.gates.get i).inputs, v < n+i.val) ∧
      (∀ G ∈ C.gates, GOk G) ∧ costG C.gates ≤ t/2 ∧
      (∀ j, tap j < n+C.gates.length) ∧
      (∀ x j, sendT C tap x j.succ = toField.symm (L j x)) ∧
      ∀ x, sendT C tap x 0 = toField.symm (c + ell (K x) + Q (K x)) := by
  classical
  obtain ⟨r,l,a,b,hr,hq⟩ := quadratic_factors t (V t) (by simp [V]) Q
  let P := emptyPlan n
  obtain ⟨D,hD,haddr⟩ := build_values (bitsN_length n) P 0 Finset.univ
    (fun j x => toField.symm (L j x)) (fun j _ E _ _ => emit_linear E (L j))
  let prod := fun (j : Fin r) (x : V n) => a j (K x) * b j (K x)
  obtain ⟨E,hE,hterms⟩ := build_values (bitsN_length n) D 1 Finset.univ
    (fun j x => toField.symm (prod j x)) (fun j _ G _ _ => emit_linproduct G ((a j).comp K) ((b j).comp K))
  obtain ⟨G,hG,hqsum⟩ := emit_sum (bitsN_length n) E Finset.univ
    (fun j x => toField.symm (prod j x)) hterms
  have hsum : evF G (fun x => ∑ j, prod j x) := by
    simpa only [evF,Equiv.apply_symm_apply] using hqsum
  obtain ⟨H,hH,hl⟩ := emit_linear G ((ell+l).comp K)
  obtain ⟨I,hI,hout⟩ := emit_addF H hl (evF_ext hsum hH)
  obtain ⟨J,hJ,hconst⟩ := emit_const (bitsN_length n) I (toField.symm c)
  obtain ⟨S,hS,hfinal⟩ := emit_addF J (f:=fun _ => c) hconst (evF_ext hout hJ)
  have hext := adds_trans (adds_trans (adds_trans (adds_trans (adds_trans hE hG) hH) hI) hJ) hS
  have cost := (adds_trans hD hext).2
  have costS : paidCount S.gates ≤ t/2 := by
    simpa [P,emptyPlan,Plan.gates,paidCount] using cost.trans (show _ ≤ t/2 by simpa [P,emptyPlan,Plan.gates,paidCount] using hr)
  obtain ⟨last,hlast,hval⟩ := hfinal
  have addrs (j : Fin h) := evaluates_ext (bitsN_length n) (haddr j (Finset.mem_univ _)) hext
  choose tp htp htv using addrs
  refine ⟨⟨S.gates,0⟩, Fin.cases last tp,S.back,S.legal,costS,Fin.cases hlast htp,?_,?_⟩
  · intro x j
    exact htv j x
  · intro x
    have := hval x
    change (S.gates.foldl appendWire (bitsN n x)).getD last false = _
    rw [this,hq]
    congr 1
    simp only [LinearMap.comp_apply,LinearMap.add_apply,prod]
    ring


def poly (n : ℕ) : Submodule F (V n → F) := by
  refine { carrier := {f | ∃ (c : F) (L : V n →ₗ[F] F) (Q : QuadraticForm F (V n)), ∀ x, f x = c + L x + Q x}, zero_mem' := ⟨0,0,0,by simp⟩, add_mem' := ?_, smul_mem' := ?_ }
  · rintro f g ⟨c,L,Q,h⟩ ⟨d,M,R,k⟩
    exact ⟨c+d,L+M,Q+R,fun x => by simp [h,k]; abel⟩
  · rintro c f ⟨d,L,Q,k⟩
    exact ⟨c*d,c•L,c•Q,fun x => by simp [k,mul_add]⟩

theorem affine_cut {n : ℕ} (a b c : V n) (hab : a ≠ b) (hac : a ≠ c) :
    ∃ (k : F) (L : V n →ₗ[F] F), k+L a = 1 ∧ k+L b = 0 ∧ k+L c = 0 := by
  obtain ⟨i,hi⟩ : ∃ i, a i ≠ b i := by by_contra! h; exact hab (funext h)
  obtain ⟨j,hj⟩ : ∃ j, a j ≠ c j := by by_contra! h; exact hac (funext h)
  by_cases e : b i = c i
  · refine ⟨b i,LinearMap.proj i,?_⟩
    change b i + a i = 1 ∧ b i + b i = 0 ∧ b i + c i = 0
    exact (show ∀ x y z : F, x ≠ y → y = z → y+x=1 ∧ y+y=0 ∧ y+z=0 by decide) _ _ _ hi e
  by_cases f : b j = c j
  · refine ⟨c j,LinearMap.proj j,?_⟩
    change c j + a j = 1 ∧ c j+b j = 0 ∧ c j+c j = 0
    exact (show ∀ x y z : F, x ≠ z → y=z → z+x=1 ∧ z+y=0 ∧ z+z=0 by decide) _ _ _ hj f
  refine ⟨b i+b j,(LinearMap.proj i : V n →ₗ[F] F) + LinearMap.proj j,?_⟩
  exact (show ∀ x y z u v w : F, x ≠ y → y ≠ z → u ≠ w → v ≠ w →
    y+v+(x+u)=1 ∧ y+v+(y+v)=0 ∧ y+v+(z+w)=0 by
    intro x y z u v w h1 h2 h3 h4; fin_cases x <;> fin_cases y <;> fin_cases z <;> fin_cases u <;> fin_cases v <;> fin_cases w <;> first | contradiction | exact ⟨rfl,rfl,rfl⟩) _ _ _ _ _ _ hi e hj f

theorem poly_indicator {n : ℕ} (a b c d : V n) (ab : a ≠ b) (ac : a ≠ c) (ad : a ≠ d) :
    ∃ p : poly n, p.val a=1 ∧ p.val b=0 ∧ p.val c=0 ∧ p.val d=0 := by
  obtain ⟨k,L,ha,hb,hc⟩ := affine_cut a b c ab ac
  obtain ⟨l,M,ha',hd,_⟩ := affine_cut a d d ad ad
  let f := fun x => (k+L x)*(l+M x)
  have hf : f ∈ poly n := ⟨k*l,k•M+l•L,QuadraticMap.linMulLin L M,fun x => by simp [f]; ring⟩
  exact ⟨⟨f,hf⟩,by simp [f,ha,ha'],by simp [f,hb],by simp [f,hc],by simp [f,hd]⟩

def phase (a : F) : ℝ := if a=0 then 1 else -1

theorem phase_zero : phase 0 = 1 := by simp [phase]
theorem phase_one : phase 1 = -1 := by simp [phase]
theorem phase_sq (a : F) : phase a * phase a = 1 := by unfold phase; split <;> norm_num
theorem phase_add (a b : F) : phase (a+b) = phase a * phase b := by
  have h : (1:F)+1=0 := by decide
  rcases eitherF a with rfl | rfl <;> rcases eitherF b with rfl | rfl <;> simp [h,phase_zero,phase_one]

noncomputable def signQ {n : ℕ} (s : poly n) (x : V n) : ℝ := phase (s.val x)

theorem shift_cancel {S : Type} [Fintype S] [AddCommGroup S] (f : S → ℝ) (d : S)
    (h : ∀ s, f (s+d) = -f s) : ∑ s, f s = 0 := by
  have he : (∑ s, f (s+d)) = ∑ s, f s := Fintype.sum_equiv (Equiv.addRight d) _ _ (fun s => rfl)
  simp_rw [h,Finset.sum_neg_distrib] at he
  linarith

theorem qpair {n : ℕ} (a b : V n) :
    (∑ s : poly n, signQ s a * signQ s b) = if a=b then (Fintype.card (poly n) : ℝ) else 0 := by
  classical
  by_cases h : a=b
  · subst b; simp [signQ,phase_sq]
  rw [if_neg h]
  obtain ⟨p,h1,h2,_,_⟩ := poly_indicator a b b b h h h
  apply shift_cancel (d:=p)
  intro s
  change phase (s.val a+p.val a)*phase (s.val b+p.val b) = _
  simp only [phase_add,h1,h2,phase_one,phase_zero,signQ]
  ring

theorem qfour_unique {n : ℕ} (a b c d : V n) (ab : a≠b) (ac : a≠c) (ad : a≠d) :
    (∑ s : poly n, signQ s a * signQ s b * signQ s c * signQ s d) = 0 := by
  obtain ⟨p,h1,h2,h3,h4⟩ := poly_indicator a b c d ab ac ad
  apply shift_cancel (d:=p)
  intro s
  change phase (s.val a+p.val a)*phase (s.val b+p.val b)*phase (s.val c+p.val c)*phase (s.val d+p.val d) = _
  simp only [phase_add,h1,h2,h3,h4,phase_one,phase_zero,signQ]
  ring


theorem qfour {n : ℕ} (a b c d : V n) :
    ∑ s : poly n, signQ s a * signQ s b * signQ s c * signQ s d =
      if a=b then (if c=d then (Fintype.card (poly n) : ℝ) else 0)
      else if a=c then (if b=d then (Fintype.card (poly n) : ℝ) else 0)
      else if a=d then (if b=c then (Fintype.card (poly n) : ℝ) else 0) else 0 := by
  have hsq (s : poly n) (x : V n) : signQ s x * signQ s x = 1 := phase_sq _
  by_cases hab : a=b
  · subst b; simp only [hsq,one_mul,ite_true]; exact qpair c d
  simp only [hab,ite_false]
  by_cases hac : a=c
  · subst c; simp only [ite_true]
    rw [← qpair b d]
    apply Finset.sum_congr rfl
    intro s _
    linear_combination (signQ s b * signQ s d) * hsq s a
  simp only [hac,ite_false]
  by_cases had : a=d
  · subst d; simp only [ite_true]
    rw [← qpair b c]
    apply Finset.sum_congr rfl
    intro s _
    linear_combination (signQ s b * signQ s c) * hsq s a
  simpa [had] using qfour_unique a b c d hab hac had

noncomputable def smix {n : ℕ} (u : V n → ℝ) (s : poly n) : ℝ := ∑ x, u x * signQ s x

theorem qsecond {n : ℕ} (u : V n → ℝ) :
    ∑ s : poly n, (smix u s)^2 = (Fintype.card (poly n) : ℝ) * ∑ x, (u x)^2 := by
  classical
  have ex (s : poly n) : (smix u s)^2 = ∑ a, ∑ b, (u a*u b) * (signQ s a * signQ s b) := by
    simp only [smix,pow_two,Finset.sum_mul,Finset.mul_sum]
    exact Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => by ring))
  simp_rw [ex]
  rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum,qpair]
  simp [mul_ite,sq,mul_comm]

theorem qweight {n : ℕ} (u : V n → ℝ) (a b c d : V n) :
    (u a*u b*u c*u d) * (∑ s : poly n, signQ s a * signQ s b * signQ s c * signQ s d) ≤
      (if d=c then if b=a then (Fintype.card (poly n) : ℝ)*(u a)^2*(u c)^2 else 0 else 0) +
      (if d=b then if c=a then (Fintype.card (poly n) : ℝ)*(u a)^2*(u b)^2 else 0 else 0) +
      (if d=a then if c=b then (Fintype.card (poly n) : ℝ)*(u a)^2*(u b)^2 else 0 else 0) := by
  have hfour (x : V n) : 0 ≤ (Fintype.card (poly n) : ℝ) * (u x)^4 := by positivity
  rw [qfour]
  split_ifs <;> subst_vars <;> simp_all only [ite_true,ite_false,not_true_eq_false,zero_add,add_zero,mul_zero] <;>
    first | ring_nf; positivity | ring_nf; rfl | nlinarith [hfour d]


theorem qfourth {n : ℕ} (u : V n → ℝ) :
    ∑ s : poly n, (smix u s)^4 ≤ (Fintype.card (poly n) : ℝ) * (3*(∑ x, (u x)^2)^2) := by
  classical
  let N := (Fintype.card (poly n) : ℝ)
  have ex (s : poly n) : (smix u s)^4 = ∑ a, ∑ b, ∑ c, ∑ d,
      (u a*u b*u c*u d) * (signQ s a * signQ s b * signQ s c * signQ s d) := by
    rw [show (smix u s)^4 = smix u s * smix u s * smix u s * smix u s by ring]
    simp only [smix,Finset.sum_mul,Finset.mul_sum]
    repeat' apply Finset.sum_congr rfl <;> intro _ _
    ring
  calc
    _ = ∑ a, ∑ b, ∑ c, ∑ d, (u a*u b*u c*u d) * (∑ s : poly n, signQ s a * signQ s b * signQ s c * signQ s d) := by
      simp_rw [ex]
      rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro a _
      rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro b _
      rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro c _
      rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro d _
      rw [Finset.mul_sum]
    _ ≤ ∑ a, ∑ b, ∑ c, ∑ d,
      ((if d=c then if b=a then N*(u a)^2*(u c)^2 else 0 else 0) +
       (if d=b then if c=a then N*(u a)^2*(u b)^2 else 0 else 0) +
       (if d=a then if c=b then N*(u a)^2*(u b)^2 else 0 else 0)) := by
      repeat' apply Finset.sum_le_sum <;> intro _ _
      apply qweight
    _ = _ := by
      simp [Finset.sum_add_distrib,Finset.sum_ite_irrel,← Finset.mul_sum,← Finset.sum_mul,N]
      ring


noncomputable def mixL {I S : Type} [Fintype I] (σ : I → S → ℝ) :
    (I → ℝ) →ₗ[ℝ] (S → ℝ) where
  toFun u s := ∑ i, u i * σ i s
  map_add' a b := by ext s; simp [add_mul,Finset.sum_add_distrib]
  map_smul' c a := by ext s; simp [mul_assoc,Finset.mul_sum]

noncomputable def valL {I : Type} [Fintype I] (a : I → ℝ) : (I → ℝ) →ₗ[ℝ] ℝ where
  toFun u := ∑ i, u i * a i
  map_add' a b := by simp [add_mul,Finset.sum_add_distrib]
  map_smul' c u := by simp [mul_assoc,Finset.mul_sum]

noncomputable def absSum (S : Type) [Fintype S] : Seminorm ℝ (S → ℝ) := by
  refine { toFun := fun f => ∑ s, |f s|, map_zero' := by simp, add_le' := ?_, neg' := ?_, smul' := ?_ }
  · intro f g; simpa [Finset.sum_add_distrib] using Finset.sum_le_sum (s:=Finset.univ) (fun s _ => abs_add_le (f s) (g s))
  · intro f; simp
  · intro c f; simp [abs_mul,Finset.mul_sum,Real.norm_eq_abs]

theorem bounded_decoder {I S : Type} [Fintype I] [Fintype S] (σ : I → S → ℝ) (a : I → ℝ)
    (h : ∀ u, valL a u ≤ absSum S (mixL σ u)) :
    ∃ d : S → ℝ, (∀ s, |d s| ≤ 1) ∧ ∀ i, ∑ s, σ i s * d s = a i := by
  classical
  let A := mixL σ
  let Z := valL a
  obtain ⟨B,hB⟩ := A.rangeRestrict.exists_rightInverse_of_surjective A.range_rangeRestrict
  have sub (v : LinearMap.range A) : A (B v) = v.val := congrArg Subtype.val (LinearMap.congr_fun hB v)
  have ker (u : I → ℝ) (hu : A u = 0) : Z u = 0 := by
    have hp : Z u ≤ absSum S (A u) := h u
    have hn : Z (-u) ≤ absSum S (A (-u)) := h (-u)
    rw [hu,map_zero] at hp
    rw [map_neg,map_neg,hu,neg_zero,map_zero] at hn
    linarith
  let f := Z.comp B
  have hd (v : LinearMap.range A) : f v ≤ absSum S v.val := by
    change Z (B v) ≤ _
    exact (h (B v)).trans_eq (congrArg (absSum S) (sub v))
  obtain ⟨g,hg,hbound⟩ := Module.Dual.exists_extension_of_le_seminorm_real (LinearMap.range A) f hd
  have he (u : I → ℝ) : g (A u) = Z u := by
    have hk := ker (B (A.rangeRestrict u)-u) (by rw [map_sub,sub]; exact sub_self _)
    rw [map_sub] at hk
    calc
      _ = f (A.rangeRestrict u) := hg _
      _ = _ := sub_eq_zero.mp hk
  refine ⟨fun s => g (Pi.single s 1),?_,?_⟩
  · intro s
    have hb := hbound (Pi.single s 1)
    change |g (Pi.single s 1)| ≤ ∑ j : S, |(Pi.single s (1:ℝ)) j| at hb
    simpa [Pi.single_apply,abs_ite] using hb
  · intro i
    have hm : A (Pi.single i 1) = σ i := by ext s; simp [A,mixL,Pi.single_apply]
    have hz : Z (Pi.single i 1) = a i := by simp [Z,valL,Pi.single_apply]
    have hs : σ i = ∑ s, σ i s • Pi.single s (1:ℝ) := by ext j; simp [Finset.sum_apply,Pi.single_apply]
    calc
      _ = g (σ i) := by conv_rhs => rw [hs,map_sum]; simp only [map_smul,smul_eq_mul]
      _ = _ := by rw [← hm,he,hz]


theorem moment_l1 {S : Type} [Fintype S] [Nonempty S] (X : S → ℝ) (Z : ℝ)
    (hz : 0 ≤ Z) (h2 : ∑ s, (X s)^2 = (Fintype.card S : ℝ)*Z)
    (h4 : ∑ s, (X s)^4 ≤ (Fintype.card S : ℝ)*(3*Z^2)) :
    (Fintype.card S : ℝ)^2*Z ≤ 3*(∑ s, |X s|)^2 := by
  let N := (Fintype.card S : ℝ)
  let M := ∑ s, |X s|
  let T := ∑ s, |X s|^3
  let V4 := ∑ s, (X s)^4
  have hn : 0 < N := by dsimp [N]; exact_mod_cast Fintype.card_pos
  have ha (x : ℝ) : |x|^2 = x^2 := sq_abs x
  have eq4 (x : ℝ) : (x^2)^2 = |x| * |x|^3 := by
    rw [← ha x]; ring
  have eq6 (x : ℝ) : (|x|^3)^2 = x^2*x^4 := by
    rw [show (|x|^3)^2 = (|x|^2)^3 by ring,ha]; ring
  have h23 : (N*Z)^2 ≤ M*T := by
    rw [← h2]
    exact Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun s _ => abs_nonneg (X s))
      (fun s _ => pow_nonneg (abs_nonneg (X s)) 3) (fun s _ => (eq4 (X s)).le)
  have h34 : T^2 ≤ (N*Z)*V4 := by
    rw [← h2]
    exact Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun s _ => sq_nonneg (X s))
      (fun s _ => by positivity) (fun s _ => (eq6 (X s)).le)
  by_cases h0 : Z=0
  · simp [h0]; positivity
  have hZ : 0 < Z := lt_of_le_of_ne hz (Ne.symm h0)
  have hu : (N*Z)^4 ≤ M^2 * ((N*Z)*(N*(3*Z^2))) := by
    calc (N*Z)^4 = ((N*Z)^2)^2 := by ring
         _ ≤ (M*T)^2 := pow_le_pow_left₀ (sq_nonneg _) h23 2
         _ = M^2 * T^2 := mul_pow M T 2
         _ ≤ M^2 * ((N*Z)*V4) := mul_le_mul_of_nonneg_left h34 (sq_nonneg M)
         _ ≤ _ := by gcongr
  change N^2*Z ≤ 3*M^2
  apply le_of_mul_le_mul_left (a := N^2*Z^3) _ (by positivity)
  nlinarith only [hu]

theorem quadratic_decoder {n : ℕ} (a : V n → ℝ) (ha : 3*(∑ i, (a i)^2) ≤ 1) :
    ∃ d : poly n → ℝ, (∀ s, |d s| ≤ 1) ∧
      ∀ i, ∑ s, signQ s i * d s = (Fintype.card (poly n) : ℝ)*a i := by
  classical
  let N := (Fintype.card (poly n) : ℝ)
  apply bounded_decoder (fun i s => signQ s i) (fun i => N*a i)
  intro u
  let Z := ∑ i, (u i)^2
  let T := ∑ i, (a i)^2
  let M := ∑ s, |smix u s|
  let v := ∑ i, u i * a i
  have mom : N^2*Z ≤ 3*M^2 := moment_l1 (smix u) Z (by dsimp [Z]; positivity) (qsecond u) (qfourth u)
  have cs : v^2 ≤ Z*T := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have hs : (N*v)^2 ≤ M^2 := by
    calc (N*v)^2 = N^2*v^2 := mul_pow _ _ 2
         _ ≤ N^2*(Z*T) := mul_le_mul_of_nonneg_left cs (sq_nonneg _)
         _ = (N^2*Z)*T := by ring
         _ ≤ (3*M^2)*T := mul_le_mul_of_nonneg_right mom (by dsimp [T]; positivity)
         _ = M^2*(3*T) := by ring
         _ ≤ M^2*1 := mul_le_mul_of_nonneg_left ha (sq_nonneg _)
         _ = _ := mul_one _
  have mpos : 0 ≤ M := by dsimp [M]; positivity
  have hl := (le_abs_self (N*v)).trans ((sq_le_sq.mp hs).trans_eq (abs_of_nonneg mpos))
  change ∑ i, u i * (N*a i) ≤ M
  calc _ = N*v := by dsimp [v]; rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => by ring)
       _ ≤ _ := hl


abbrev Aut (n : ℕ) := V n ≃ₗ[F] V n

theorem move_nonzero {n : ℕ} (u v : V n) (hu : u ≠ 0) (hv : v ≠ 0) :
    ∃ e : Aut n, e u = v := by
  obtain ⟨k,L,hk,hl,hm⟩ := affine_cut (0:V n) u v hu.symm hv.symm
  have h1 : k=1 := by simpa using hk
  have lu : L u=1 := (show ∀ x : F, 1+x=0 → x=1 by decide) _ (h1 ▸ hl)
  have lv : L v=1 := (show ∀ x : F, 1+x=0 → x=1 by decide) _ (h1 ▸ hm)
  let T : V n →ₗ[F] V n := LinearMap.id + L.smulRight (u+v)
  have zero2 : (1:F)+1=0 := by decide
  have lf (x : V n) : L (T x) = L x := by simp [T,lu,lv,zero2]; exact (show ∀ a : F, a+a=0 by decide) (L x)
  have inv : Function.Involutive T := by
    intro x
    change T x + L (T x) • (u+v) = x
    rw [lf]
    change (x + L x • (u+v)) + L x • (u+v) = x
    rw [add_assoc,← add_smul,show L x+L x=0 from (show ∀ a : F, a+a=0 by decide) (L x),zero_smul,add_zero]
  refine ⟨LinearEquiv.ofBijective T inv.bijective,?_⟩
  change u + L u • (u+v) = v
  have hu0 : u+u=0 := by ext j; exact (show ∀ a : F, a+a=0 by decide) (u j)
  rw [lu,one_smul,← add_assoc,hu0,zero_add]

noncomputable def collN {n h t : ℕ} [Fintype (Aut n)] (R : V n ≃ₗ[F] V h × V t) (v : V n) : ℚ :=
  ∑ e : Aut n, if (R (e v)).1=0 then 1 else 0

theorem hash_collision {n h t : ℕ} [Fintype (Aut n)] (R : V n ≃ₗ[F] V h × V t)
    (hn : n=h+t) (x z : V n) (hx : x ≠ z) :
    (2:ℚ)^h * (∑ e : Aut n, if (R (e x)).1 = (R (e z)).1 then (1:ℚ) else 0) ≤
      (Fintype.card (Aut n) : ℚ) := by
  classical
  let d := x-z
  have hdn : d≠0 := sub_ne_zero.mpr hx
  have minc (w : V n) : collN R d ≤ collN R w := by
    by_cases hw : w=0
    · subst w; unfold collN; apply Finset.sum_le_sum; intro e _; split <;> simp
    obtain ⟨g,hg⟩ := move_nonzero d w hdn hw
    let perm : Aut n ≃ Aut n := {
      toFun := fun e => g.trans e
      invFun := fun e => g.symm.trans e
      left_inv := fun e => by ext i; simp
      right_inv := fun e => by ext i; simp }
    let f := fun e : Aut n => if (R (e d)).1=0 then (1:ℚ) else 0
    apply le_of_eq
    calc collN R d = ∑ e : Aut n, f (perm e) := (Equiv.sum_comp perm f).symm
         _ = _ := by simp [collN,f,perm,hg]
  have per (e : Aut n) : (∑ d : V n, if (R (e d)).1=0 then (1:ℚ) else 0) = 2^t := by
    let f := fun p : V h × V t => if p.1=0 then (1:ℚ) else 0
    calc _ = ∑ p : V h × V t, f p := Equiv.sum_comp (e.trans R).toEquiv f
         _ = _ := by
           rw [Fintype.sum_prod_type]
           trans ∑ a : V h, if a=0 then (2:ℚ)^t else 0
           · apply Finset.sum_congr rfl; intro a _; by_cases ha : a=0 <;> simp [f,ha,cardV]
           · simp
  have total : (∑ v : V n, collN R v) = (Fintype.card (Aut n):ℚ) * 2^t := by
    unfold collN
    rw [Finset.sum_comm]
    simp_rw [per]
    simp
  have cm : (2:ℚ)^n * collN R d ≤ (Fintype.card (Aut n):ℚ) * 2^t := by
    calc _ = ∑ _w : V n, collN R d := by simp [cardV]
         _ ≤ _ := Finset.sum_le_sum (fun w _ => minc w)
         _ = _ := total
  have eq : (∑ e : Aut n, if (R (e x)).1 = (R (e z)).1 then (1:ℚ) else 0) = collN R d := by
    simp [collN,d,sub_eq_zero]
  rw [eq]
  apply le_of_mul_le_mul_right (a:=(2:ℚ)^t) _ (by positivity)
  rw [show (2:ℚ)^n = 2^h*2^t by rw [hn,pow_add]] at cm
  linarith only [cm]


theorem round_orthogonal {I S : Type} [Fintype I] [Fintype S] [Nonempty S] [DecidableEq I]
    (σ : I → S → ℚ) (a : I → ℚ) (d : S → ℝ) (hb : ∀ s, |d s| ≤ 31/32)
    (hs : ∀ i s, |σ i s| = 1)
    (hp : ∀ i j, ∑ s, σ i s * σ j s = if i=j then (Fintype.card S : ℚ) else 0)
    (hd : ∀ i, ∑ s, (σ i s : ℝ)*d s = (Fintype.card S : ℝ)*a i) :
    ∃ c : S → ℚ, (∀ s, |c s| ≤ 1) ∧ ∀ i, ∑ s, σ i s*c s = (Fintype.card S : ℚ)*a i := by
  classical
  let N := (Fintype.card S : ℚ)
  let ε := 1/(64*((Fintype.card I : ℝ)+1))
  have heps : 0 < ε := by dsimp [ε]; positivity
  have hn : (0:ℚ) < N := by dsimp [N]; exact_mod_cast Fintype.card_pos
  have hnr : (0:ℝ) < (N:ℝ) := by exact_mod_cast hn
  have hex (s : S) : ∃ v : ℚ, |(v:ℝ)-d s| ≤ ε := by
    obtain ⟨v,hv1,hv2⟩ := exists_rat_btwn (show d s-ε < d s+ε by linarith)
    exact ⟨v,abs_le.mpr ⟨by linarith,by linarith⟩⟩
  choose v hv using hex
  let err := fun i => a i - (∑ s, σ i s * v s)/N
  have hcast (i s) : |(σ i s : ℝ)| = 1 := by exact_mod_cast hs i s
  have herr (i : I) : |(err i : ℝ)| ≤ ε := by
    have he : (N:ℝ) * (err i : ℝ) = ∑ s, (σ i s : ℝ)*(d s-v s) := by
      simp only [mul_sub,Finset.sum_sub_distrib,hd,err,Rat.cast_sub,Rat.cast_div,Rat.cast_sum,Rat.cast_mul]
      have hncast : (N:ℝ) = (Fintype.card S : ℝ) := by simp [N]
      rw [← hncast]
      field_simp
    apply le_of_mul_le_mul_left (a:=(N:ℝ)) _ hnr
    calc (N:ℝ)*|(err i:ℝ)| = |(N:ℝ)*(err i:ℝ)| := by rw [abs_mul,abs_of_pos hnr]
         _ = _ := congrArg abs he
         _ ≤ ∑ s, |(σ i s:ℝ)*(d s-v s)| := Finset.abs_sum_le_sum_abs _ _
         _ ≤ ∑ _s : S, ε := Finset.sum_le_sum (fun s _ => by rw [abs_mul,hcast,one_mul,abs_sub_comm]; exact hv s)
         _ = _ := by simp [N]
  refine ⟨fun s => v s + ∑ i, σ i s*err i,?_,?_⟩
  · intro s
    have hv1 : |(v s:ℝ)| ≤ 31/32+ε := by
      have tmp := abs_add_le ((v s:ℝ)-d s) (d s)
      rw [sub_add_cancel] at tmp
      linarith [hv s,hb s]
    have hcorr : |∑ i, (σ i s:ℝ)*(err i:ℝ)| ≤ (Fintype.card I:ℝ)*ε := by
      calc _ ≤ ∑ i, |(σ i s:ℝ)*(err i:ℝ)| := Finset.abs_sum_le_sum_abs _ _
           _ ≤ ∑ _i : I, ε := Finset.sum_le_sum (fun i _ => by rw [abs_mul,hcast,one_mul]; exact herr i)
           _ = _ := by simp
    have he0 : ((Fintype.card I:ℝ)+1)*ε = 1/64 := by dsimp [ε]; field_simp
    have hrat : |(v s:ℝ)+∑ i, (σ i s:ℝ)*(err i:ℝ)| ≤ 1 := by
      have h := abs_add_le (v s:ℝ) (∑ i, (σ i s:ℝ)*(err i:ℝ))
      nlinarith only [h,hv1,hcorr,he0]
    exact_mod_cast hrat
  · intro i
    calc
      _ = (∑ s, σ i s * v s) + ∑ j, (∑ s, σ i s * σ j s)*err j := by
        simp only [mul_add,Finset.sum_add_distrib,Finset.mul_sum,Finset.sum_mul]
        rw [Finset.sum_comm (f:=fun s j => σ i s * (σ j s * err j))]
        simp [mul_assoc]
      _ = (∑ s, σ i s * v s) + N*err i := by simp [hp,ite_mul,N]
      _ = _ := by dsimp only [err]; field_simp [hn.ne']; dsimp [N]; ring


def gain (v : ℚ) : ℚ := (31/16)/(1+3*v)

noncomputable def bucketMass {I B : Type} [Fintype I] [DecidableEq B] (A : I → B) (w : I → ℚ) (b : B) : ℚ :=
  ∑ z, (w z)^2 * (if A z=b then 1 else 0)

theorem gain_average {I S B : Type} [Fintype I] [Fintype S] [DecidableEq B]
    (A : S → I → B) (w : I → ℚ) (x : I) (H : ℚ) (hH : 0 < H)
    (hl : 0 ≤ w x) (hh : w x ≤ 1/2) (mass : 16*(∑ z, (w z)^2) ≤ H)
    (col : ∀ z, z≠x → H*(∑ s, if A s z=A s x then (1:ℚ) else 0) ≤ Fintype.card S) :
    (Fintype.card S : ℚ) ≤ ∑ s, gain (bucketMass (A s) w (A s x)) := by
  classical
  let N := (Fintype.card S : ℚ)
  have hn : 0 ≤ N := Nat.cast_nonneg _
  have c (z : I) : (∑ s, if A s z=A s x then (1:ℚ) else 0) ≤ N/H + if z=x then N else 0 := by
    by_cases hz : z=x
    · subst z; simp [N]; positivity
    · rw [if_neg hz,add_zero]
      apply (le_div_iff₀ hH).2
      simpa [mul_comm] using col z hz
  let V0 := fun s => bucketMass (A s) w (A s x)
  have htotal : ∑ s, V0 s ≤ N*(5/16) := by
    have ex : ∑ s, V0 s = ∑ z, (w z)^2*(∑ s, if A s z=A s x then (1:ℚ) else 0) := by
      dsimp only [V0,bucketMass]; rw [Finset.sum_comm]; simp only [Finset.mul_sum]
    rw [ex]
    calc _ ≤ ∑ z, (w z)^2 * (N/H + if z=x then N else 0) :=
              Finset.sum_le_sum (fun z _ => mul_le_mul_of_nonneg_left (c z) (sq_nonneg _))
         _ = (∑ z, (w z)^2)*(N/H) + (w x)^2*N := by simp [mul_add,mul_ite,Finset.sum_add_distrib,Finset.sum_mul]
         _ ≤ (H/16)*(N/H) + (1/2)^2*N := by
              gcongr
              · linarith
         _ = _ := by field_simp; ring
  have vpos s : 0 ≤ V0 s := by
    unfold V0 bucketMass; exact Finset.sum_nonneg (fun z _ => mul_nonneg (sq_nonneg _) (by split <;> norm_num))
  have tan (s : S) : 1 - (48/31)*(V0 s-5/16) ≤ gain (V0 s) := by
    apply (le_div_iff₀ (show 0 < 1+3*V0 s by linarith [vpos s])).2
    nlinarith [sq_nonneg (V0 s-5/16)]
  have summ := Finset.sum_le_sum (s:=Finset.univ) (fun s _ => tan s)
  simp only [Finset.sum_sub_distrib,← Finset.mul_sum,Finset.sum_const,Finset.card_univ,
    nsmul_eq_mul,mul_one] at summ
  change N ≤ ∑ s, gain (V0 s)
  change N-48/31*(∑ s, V0 s - _ ) ≤ _ at summ
  linarith


def signR {n : ℕ} (p : poly n) (x : V n) : ℚ := if p.val x=0 then 1 else -1

theorem sign_cast {n : ℕ} (p : poly n) (x : V n) : (signR p x : ℝ) = signQ p x := by
  by_cases h : p.val x = 0 <;> simp [signR,signQ,phase,h]

theorem rational_bucket {n : ℕ} (a : V n → ℚ) :
    ∃ d : poly n → ℚ, (∀ s, |d s| ≤ 1) ∧
      ∀ i, ∑ s, signR s i * d s = (Fintype.card (poly n) : ℚ) * (gain (∑ j, (a j)^2) * a i) := by
  classical
  let S := ∑ i, (a i)^2
  let c : ℚ := 2/(1+3*S)
  have hs : 0 ≤ S := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hpos : 0 < 1+3*S := by linarith
  have hh : 3 * ∑ i, (c*a i)^2 ≤ 1 := by
    simp only [mul_pow,← Finset.mul_sum]
    change 3*(c^2*S) ≤ 1
    dsimp [c]
    field_simp
    nlinarith [sq_nonneg (1-3*S)]
  obtain ⟨d,hb,hc⟩ := quadratic_decoder (fun i => ((c*a i:ℚ):ℝ)) (by exact_mod_cast hh)
  apply round_orthogonal (fun i s => signR s i) (fun i => gain S*a i) (fun s => (31/32)*d s)
  · intro s
    rw [abs_mul,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 31/32)]
    nlinarith [hb s]
  · intro i s
    unfold signR; split <;> norm_num
  · intro i j
    have hc2 := qpair i j
    by_cases h : i=j <;> simp only [h,ite_true,ite_false] at hc2 ⊢ <;>
      simp_rw [← sign_cast] at hc2 <;> exact_mod_cast hc2
  · intro i
    calc (∑ s, (signR s i : ℝ) * (31/32 * d s)) = (31/32)*∑ s, signQ s i*d s := by
           rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro s _; rw [sign_cast]; ring
         _ = _ := by
           rw [hc i]
           simp [c,gain]
           ring


def bs (b : Bool) : ℚ := if b then -1 else 1

theorem bs_sq (b : Bool) : bs b * bs b = 1 := by cases b <;> norm_num [bs]
theorem abs_bs (b : Bool) : |bs b| = 1 := by cases b <;> norm_num [bs]

noncomputable def listVal {I B : Type} [DecidableEq B] (A : I → B) (tru : I → Bool)
    (D : Finset I) (b : B) (base : ℚ) : ℚ := by
  classical
  exact if h : ∃ z ∈ D, A z=b then bs (tru (Classical.choose h)) else base

theorem listVal_bound {I B : Type} [DecidableEq B] (A : I → B) (tru : I → Bool)
    (D : Finset I) (b : B) (base : ℚ) (hb : |base|≤1) : |listVal A tru D b base| ≤ 1 := by
  unfold listVal; split <;> simp [abs_bs,hb]

theorem list_point {I B : Type} [DecidableEq I] [DecidableEq B]
    (A : I → B) (tru : I → Bool) (x : I) (D : Finset I) (base : ℚ) (hb : |base|≤1) :
    (if x∈D then 1 else bs (tru x)*base) - 2*(((D.erase x).filter (fun z => A z=A x)).card : ℚ) ≤
      bs (tru x) * listVal A tru D (A x) base := by
  classical
  let E := (D.erase x).filter (fun z => A z=A x)
  by_cases hz : E.card=0
  · have alone (z : I) (hd : z∈D) (he : A z=A x) : z=x := by
      by_contra hn
      have hm : z∈E := Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hn,hd⟩,he⟩
      exact (Nat.ne_of_gt (Finset.card_pos.mpr ⟨z,hm⟩)) hz
    change (if x∈D then 1 else bs (tru x)*base) - 2*(E.card:ℚ) ≤ _
    simp only [hz,Nat.cast_zero,mul_zero,sub_zero]
    by_cases hx : x∈D
    · have h : ∃ z∈D, A z=A x := ⟨x,hx,rfl⟩
      have hc := Classical.choose_spec h
      simp [listVal,hx,h,alone _ hc.1 hc.2,bs_sq]
    · have h : ¬∃ z∈D, A z=A x := by rintro ⟨z,hd,he⟩; exact hx (alone z hd he ▸ hd)
      simp [listVal,hx,h]
  · have he : (1:ℚ) ≤ E.card := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hz
    have hb2 := (abs_le.mp (show |bs (tru x) * listVal A tru D (A x) base| ≤ 1 by rw [abs_mul,abs_bs,one_mul]; exact listVal_bound _ _ _ _ _ hb)).1
    have hb1 := (abs_le.mp (show |bs (tru x)*base| ≤ 1 by simpa [abs_mul,abs_bs] using hb)).2
    change (if x∈D then 1 else bs (tru x)*base) - 2*(E.card:ℚ) ≤ _
    split <;> linarith

theorem list_average {I S B : Type} [Fintype S] [DecidableEq I] [DecidableEq B]
    (A : S → I → B) (x : I) (D : Finset I) (H : ℚ) (hH : 0 < H)
    (col : ∀ z, z≠x → H*(∑ s, if A s z=A s x then (1:ℚ) else 0) ≤ Fintype.card S) :
    (∑ e, (((D.erase x).filter (fun z => A e z=A e x)).card : ℚ)) ≤
      (D.card:ℚ)*(Fintype.card S:ℚ)/H := by
  classical
  calc _ = ∑ z ∈ D.erase x, ∑ e, if A e z=A e x then (1:ℚ) else 0 := by
             simp_rw [Finset.natCast_card_filter]; rw [Finset.sum_comm]
       _ ≤ ∑ _z ∈ D.erase x, (Fintype.card S:ℚ)/H := Finset.sum_le_sum (fun z hz => by
             apply (le_div_iff₀ hH).2; simpa [mul_comm] using col z (Finset.ne_of_mem_erase hz))
       _ ≤ _ := by
             rw [Finset.sum_const,nsmul_eq_mul,← mul_div_assoc]
             have hcard : (D.erase x).card ≤ D.card := Finset.card_le_card (Finset.erase_subset _ _)
             exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (Nat.cast_nonneg _)) hH.le


theorem list_total {I S B Q : Type} [Fintype S] [Fintype Q] [DecidableEq I] [DecidableEq B]
    (A : S → I → B) (tru : I → Bool) (x : I) (D : Finset I) (H w : ℚ) (hH : 0 < H)
    (base : S → Q → ℚ) (hb : ∀ s q, |base s q| ≤ 1)
    (lo : w * ((Fintype.card S:ℚ)*Fintype.card Q) ≤ ∑ s, ∑ q, bs (tru x)*base s q)
    (col : ∀ z, z≠x → H*(∑ s, if A s z=A s x then (1:ℚ) else 0) ≤ Fintype.card S) :
    ((if x∈D then 1 else w) - 2*D.card/H) * ((Fintype.card S:ℚ)*Fintype.card Q) ≤
      ∑ s, ∑ q, bs (tru x)*listVal (A s) tru D (A s x) (base s q) := by
  classical
  let E := fun s => (((D.erase x).filter (fun z => A s z=A s x)).card : ℚ)
  let N := (Fintype.card S : ℚ)
  let M := (Fintype.card Q : ℚ)
  let raw := fun s q => if x∈D then 1 else bs (tru x)*base s q
  have hpoint (s : S) (q : Q) : raw s q - 2*E s ≤ bs (tru x)*listVal (A s) tru D (A s x) (base s q) :=
    list_point (A s) tru x D _ (hb s q)
  have hraw : (if x∈D then 1 else w)*(N*M) ≤ ∑ s, ∑ q, raw s q := by
    by_cases hx : x∈D
    · simp [hx,raw,N,M]
    · simpa only [hx,ite_false,raw] using lo
  have herr : ∑ s, ∑ _q : Q, 2*E s ≤ (2*D.card/H)*(N*M) := by
    have he := list_average A x D H hH col
    change (∑ e, E e) ≤ (D.card:ℚ)*N/H at he
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,← Finset.mul_sum]
    change M * (2 * ∑ e, E e) ≤ _
    calc _ ≤ M*(2*((D.card:ℚ)*N/H)) := by gcongr
         _ = _ := by ring
  have agg := Finset.sum_le_sum (s:=Finset.univ) (fun s _ => Finset.sum_le_sum (s:=Finset.univ) (fun q _ => hpoint s q))
  simp only [Finset.sum_sub_distrib] at agg
  change ((if x∈D then 1 else w) - 2*D.card/H) * (N*M) ≤ _
  linarith


def IsInt (q : ℚ) : Prop := ∃ i : ℤ, (i : ℚ) = q

theorem count_lt (N : ℕ) (θ : ℚ) (hint : IsInt θ) (h0 : 0 ≤ θ) (h1 : θ ≤ N) :
    ((Finset.univ.filter (fun r : Fin N => (r.val : ℚ) < θ)).card : ℚ) = θ := by
  obtain ⟨i, rfl⟩ := hint
  have hi : 0 ≤ i := by exact_mod_cast h0
  lift i to ℕ using hi
  have hj : i ≤ N := by exact_mod_cast h1
  have h2 : (Finset.univ.filter (fun r : Fin N => (r.val : ℚ) < ((i : ℤ) : ℚ)))
      = Finset.univ.filter (fun r : Fin N => r.val < i) := by
    ext r
    simp
  rw [h2, Fin.card_filter_val_lt, min_eq_right hj]
  simp


theorem denominators {I : Type} [Fintype I] (v : I → ℚ) :
    ∃ B : ℕ, 0 < B ∧ ∀ i, IsInt ((B:ℚ)*v i) := by
  refine ⟨∏ i, (v i).den,Finset.prod_pos (fun i _ => Rat.den_pos _),?_⟩
  intro i
  obtain ⟨c,hc⟩ := Finset.dvd_prod_of_mem (fun j => (v j).den) (Finset.mem_univ i)
  refine ⟨c*(v i).num,?_⟩
  rw [hc]; push_cast
  linear_combination (-(c:ℚ))*Rat.mul_den_eq_num (v i)

theorem uniform_coin {I : Type} [Fintype I] (p : I → ℚ) (hp : ∀ i, |p i| ≤ 1) :
    ∃ (N : ℕ) (read : I → Fin N → Bool), 0 < N ∧ ∀ i, ∑ r, bs (read i r) = (N:ℚ)*p i := by
  let prob := fun i => (1-p i)/2
  obtain ⟨N,hN,hi⟩ := denominators prob
  let read := fun (i : I) (r : Fin N) => decide ((r.val:ℚ) < (N:ℚ)*prob i)
  refine ⟨N,read,hN,?_⟩
  intro i
  have h0 := (abs_le.mp (hp i)).1
  have h1 := (abs_le.mp (hp i)).2
  have hN0 : (0:ℚ) ≤ N := Nat.cast_nonneg _
  have pp : (0:ℚ) ≤ prob i := by dsimp [prob]; linarith
  have pp1 : prob i ≤ 1 := by dsimp [prob]; linarith
  have cnt := count_lt N ((N:ℚ)*prob i) (hi i) (mul_nonneg hN0 pp)
    (by simpa using mul_le_mul_of_nonneg_left pp1 hN0)
  have he (r : Fin N) : bs (read i r) = 1-2*(if (r.val:ℚ)<(N:ℚ)*prob i then (1:ℚ) else 0) := by
    by_cases h : (r.val:ℚ)<(N:ℚ)*prob i <;> norm_num [read,bs,h]
  simp_rw [he]
  rw [Finset.sum_sub_distrib,← Finset.mul_sum,← Finset.sum_filter]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one,cnt]
  dsimp only [prob]; ring

theorem sc_bs (a b : Bool) : sc a b = bs a * bs b := by cases a <;> cases b <;> norm_num [sc,bs]

theorem pack {S X Y M : Type} [Fintype S] [Nonempty S] [Fintype Y] [Fintype M]
    (send : S → X → M) (truth : X → Y → Bool) (bias : X → Y → ℚ) (p : S → M → Y → ℚ)
    (hb : ∀ s m y, |p s m y| ≤ 1)
    (hs : ∀ x y, bias x y * (Fintype.card S : ℚ) ≤ ∑ s, bs (truth x y)*p s (send s x) y) :
    ∃ (z : ℕ) (sel : Fin z → S) (rd : Fin z → M → Y → Bool), 0 < z ∧ ∀ x y,
      (1+bias x y)*(z:ℚ) ≤ 2*(((Finset.univ : Finset (Fin z)).filter (fun i => rd i (send (sel i) x) y = truth x y)).card : ℚ) := by
  classical
  obtain ⟨N,coin,hN,hcoin⟩ := uniform_coin (fun a : S × M × Y => p a.1 a.2.1 a.2.2)
    (fun a => hb a.1 a.2.1 a.2.2)
  let Ω := S × Fin N
  let z := Fintype.card Ω
  let e : Ω ≃ Fin z := Fintype.equivFin _
  let sel := fun i => (e.symm i).1
  let rd := fun i m y => coin (sel i,m,y) (e.symm i).2
  have hz : z = Fintype.card S * N := by simp [z,Ω]
  refine ⟨z,sel,rd,by rw [hz]; exact Nat.mul_pos Fintype.card_pos hN,?_⟩
  intro x y
  let f := fun ω : Ω => sc (coin (ω.1,send ω.1 x,y) ω.2) (truth x y)
  have hsum : ∑ i, sc (rd i (send (sel i) x) y) (truth x y) = (N:ℚ)*∑ s, bs (truth x y)*p s (send s x) y := by
    calc _ = ∑ ω : Ω, f ω := Equiv.sum_comp e.symm f
         _ = _ := by
           rw [Fintype.sum_prod_type,Finset.mul_sum]
           apply Finset.sum_congr rfl; intro s _
           simp only [f,sc_bs,← Finset.sum_mul,hcoin]
           ring
  have hcnt := sum_sc (fun i => rd i (send (sel i) x) y) (truth x y)
  rw [hsum] at hcnt
  have h := mul_le_mul_of_nonneg_left (hs x y) (Nat.cast_nonneg N : (0:ℚ)≤N)
  have hZ : (z:ℚ)=(Fintype.card S:ℚ)*N := by exact_mod_cast hz
  rw [hZ] at hcnt ⊢
  linarith


theorem bucket_profile {n h t : ℕ} (T : V n ≃ₗ[F] V h × V t) (w : V n → ℚ) (b : V h) :
    bucketMass (fun x => (T x).1) w b = ∑ r : V t, (w (T.symm (b,r)))^2 := by
  classical
  calc _ = ∑ p : V h × V t, (w (T.symm p))^2*(if p.1=b then 1 else 0) :=
             Fintype.sum_equiv T.toEquiv _ _ (fun x => by simp)
       _ = _ := by
             rw [Fintype.sum_prod_type]
             trans ∑ a : V h, if a=b then (∑ z : V t, (w (T.symm (b,z)))^2) else 0
             · apply Finset.sum_congr rfl; intro a _; by_cases ha : a=b <;> simp [ha]
             · simp

noncomputable def msgH {n h t : ℕ} (R : V n ≃ₗ[F] V h × V t) (s : Aut n × poly t) (x : V n) : V h × Bool :=
  ((R (s.1 x)).1, toField.symm (s.2.val (R (s.1 x)).2))

theorem soft_protocol {n h t k : ℕ} [Fintype (Aut n)] (R : V n ≃ₗ[F] V h × V t) (hn : n=h+t)
    (truth : V n → Fin k → Bool) (w : V n → Fin k → ℚ) (D : Fin k → Finset (V n))
    (hw : ∀ x y, 0 ≤ w x y ∧ w x y ≤ 1/2) (mass : ∀ y, 16*(∑ x, (w x y)^2) ≤ (2:ℚ)^h) :
    ∃ p : (Aut n × poly t) → (V h × Bool) → Fin k → ℚ,
      (∀ s m y, |p s m y| ≤ 1) ∧ ∀ x y,
        ((if x∈D y then 1 else w x y)-2*(D y).card/(2:ℚ)^h) * (Fintype.card (Aut n × poly t):ℚ) ≤
          ∑ s, bs (truth x y)*p s (msgH R s x) y := by
  classical
  let E := fun e : Aut n => e.trans R
  let A := fun (e : Aut n) (x : V n) => (E e x).1
  let K := fun (e : Aut n) (x : V n) => (E e x).2
  let X := fun (e : Aut n) (b : V h) (r : V t) => (E e).symm (b,r)
  have get (e : Aut n) (x : V n) : X e (A e x) (K e x) = x := by simp [X,A,K]
  let a := fun e b y r => bs (truth (X e b r) y) * w (X e b r) y
  have en (e b y) : (∑ r, (a e b y r)^2) = bucketMass (A e) (fun z => w z y) b := by
    rw [bucket_profile (E e)]
    have hb (v:Bool) : (bs v)^2=1 := by rw [pow_two,bs_sq]
    simp [a,X,mul_pow,hb]
  have hex (e : Aut n) (b : V h) (y : Fin k) := rational_bucket (a e b y)
  choose raw hbd hcorr using hex
  let base := fun (s : Aut n × poly t) (m : V h × Bool) (y : Fin k) => bs m.2 * raw s.1 m.1 y s.2
  let p := fun (s : Aut n × poly t) (m : V h × Bool) (y : Fin k) =>
    listVal (A s.1) (fun z => truth z y) (D y) m.1 (base s m y)
  have hb (s m y) : |base s m y| ≤ 1 := by dsimp [base]; rw [abs_mul,abs_bs,one_mul]; exact hbd _ _ _ _
  refine ⟨p,fun s m y => listVal_bound _ _ _ _ _ (hb s m y),?_⟩
  intro x y
  have col (z : V n) (hz : z≠x) : (2:ℚ)^h*(∑ e, if A e z=A e x then (1:ℚ) else 0) ≤ Fintype.card (Aut n) :=
    hash_collision R hn z x hz
  have avg := gain_average A (fun z => w z y) x ((2:ℚ)^h) (by positivity) (hw x y).1 (hw x y).2 (mass y) col
  let N := (Fintype.card (poly t):ℚ)
  have signBit (q : poly t) (z : V t) : bs (toField.symm (q.val z)) = signR q z := by
    rcases eitherF (q.val z) with he | he <;> norm_num [signR,he,bs,toField]
  have per (e : Aut n) : (∑ q : poly t, bs (truth x y)*base (e,q) (msgH R (e,q) x) y) =
      N*(gain (bucketMass (A e) (fun z => w z y) (A e x)) * w x y) := by
    change (∑ q : poly t, bs (truth x y) * (bs (toField.symm (q.val (K e x))) * raw e (A e x) y q)) = _
    simp_rw [signBit]
    rw [← Finset.mul_sum,hcorr,en]
    dsimp only [a]
    rw [get]
    change bs (truth x y) * (N * (_ * (bs (truth x y) * w x y))) = _
    linear_combination (N*gain (bucketMass (A e) (fun z => w z y) (A e x))*w x y)*bs_sq (truth x y)
  have lo : w x y * ((Fintype.card (Aut n):ℚ)*N) ≤ ∑ e, ∑ q : poly t, bs (truth x y)*base (e,q) (msgH R (e,q) x) y := by
    simp_rw [per]
    rw [← Finset.mul_sum,← Finset.sum_mul]
    calc _ = N*((Fintype.card (Aut n):ℚ)*w x y) := by ring
         _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right avg (hw x y).1) (Nat.cast_nonneg _)
  have result := list_total A (fun z => truth z y) x (D y) ((2:ℚ)^h) (w x y) (by positivity)
    (fun e q => base (e,q) (msgH R (e,q) x) y) (fun e q => hb _ _ _) lo col
  rw [Fintype.card_prod,Nat.cast_mul,Fintype.sum_prod_type]
  exact result


def msgDecode {h : ℕ} (m : Fin (h+1) → Bool) : V h × Bool := (fun j => toField (m j.succ),m 0)

theorem synth_message {n h t : ℕ} (R : V n ≃ₗ[F] V h × V t) (s : Aut n × poly t) :
    ∃ (C : Circuit) (tap : Fin (h+1) → ℕ),
      (∀ i : Fin C.gates.length, ∀ v ∈ (C.gates.get i).inputs, v<n+i.val) ∧
      (∀ G ∈ C.gates, GOk G) ∧ costG C.gates ≤ t/2 ∧
      (∀ j, tap j < n+C.gates.length) ∧ ∀ x, msgDecode (sendT C tap x) = msgH R s x := by
  obtain ⟨c,l,Q,hq⟩ := s.2.property
  let E := (s.1.trans R).toLinearMap
  let L : Fin h → (V n →ₗ[F] F) := fun j => (LinearMap.proj j).comp ((LinearMap.fst F (V h) (V t)).comp E)
  let K := (LinearMap.snd F (V h) (V t)).comp E
  obtain ⟨C,tap,hb,ho,hc,ht,haddr,hquad⟩ := compile_message L K c l Q
  refine ⟨C,tap,hb,ho,hc,ht,?_⟩
  intro x
  apply Prod.ext
  · funext j
    change toField (sendT C tap x j.succ) = _
    rw [haddr,Equiv.apply_symm_apply]; rfl
  · change sendT C tap x 0 = toField.symm (s.2.val _)
    rw [hquad,hq]; rfl

theorem upper (n h : ℕ) (hle : h ≤ n) : Universal n h ((n-h)/2) := by
  classical
  intro k truth w D hw hm
  let t := n-h
  have hn : n=h+t := by dsimp [t]; omega
  let R : V n ≃ₗ[F] V h × V t := LinearEquiv.ofFinrankEq _ _ (by simp [V,Module.finrank_prod,hn])
  let E := boolEquiv n
  let tru := fun (x : V n) (y : Fin k) => truth (E x) y
  let wt := fun (x : V n) (y : Fin k) => min (w (E x) y) (1/2:ℚ)
  let des := fun (y : Fin k) => (D y).map E.symm.toEmbedding
  have hcwt (x y) : 0 ≤ wt x y ∧ wt x y ≤ 1/2 :=
    ⟨le_min (hw _ _) (by norm_num),min_le_right _ _⟩
  have mass (y) : 16*(∑ x : V n, (wt x y)^2) ≤ (2:ℚ)^h := by
    have hb (x : V n) : (wt x y)^2 ≤ (w (E x) y)^2 :=
      pow_le_pow_left₀ (hcwt x y).1 (min_le_left _ _) 2
    calc _ ≤ 16*∑ x : V n, (w (E x) y)^2 := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun x _ => hb x)) (by norm_num)
         _ = 16*∑ x : Fin n → Bool, (w x y)^2 := by rw [Equiv.sum_comp E (fun x => (w x y)^2)]
         _ ≤ _ := by simpa using hm y
  letI : Finite (Aut n) := Finite.of_injective (fun e : Aut n => (e : V n → V n))
    (fun e f he => LinearEquiv.ext (fun x => congrFun he x))
  letI : Fintype (Aut n) := Fintype.ofFinite _
  letI : Nonempty (Aut n) := ⟨LinearEquiv.refl F (V n)⟩
  obtain ⟨p,hp,hsoft⟩ := soft_protocol R hn tru wt des hcwt mass
  let bias := fun x y => ((if x∈des y then 1 else wt x y)-2*(des y).card/(2:ℚ)^h)
  obtain ⟨z,sel,rd,hz,hpred⟩ := pack (msgH R) tru bias p hp hsoft
  choose C tap hback hops hcost htaps hmsg using synth_message R
  refine ⟨z,fun i => C (sel i),fun i => tap (sel i),fun i msg y => rd i (msgDecode msg) y,hz,?_,?_⟩
  · intro i
    exact ⟨⟨hback _,hops _⟩,hcost _,htaps _⟩
  · intro xb y
    let x := E.symm xb
    have ex : E x=xb := E.apply_symm_apply _
    have he : x∈des y ↔ xb∈D y := by simp [des,x]
    have hcard : (des y).card=(D y).card := Finset.card_map _
    have hbits : bitsN n x = List.ofFn xb := congrArg List.ofFn ex
    have hdecode (i : Fin z) : msgDecode (fun j => ((C (sel i)).wires (List.ofFn xb)).getD (tap (sel i) j) false) = msgH R (sel i) x := by
      rw [← hbits]
      exact hmsg (sel i) x
    have hh := hpred x y
    simp only [bias,he,hcard,wt,tru,ex,← add_sub_assoc] at hh
    simpa only [hdecode] using hh


end PEqualNP.Outside.L_lib_1044_aux

theorem PEqualNP.Outside.L_lib_1044 : (∀ (n h : Nat), h ≤ n →
  let t := n-h
  let W := Fin n → Bool
  let H := 2^h
  let Circ := PEqualNP.CircuitLowerBounds.Circuit
  let legal := fun (C : Circ) =>
    (∀ i : Fin C.gates.length, ∀ v ∈ (C.gates.get i).inputs, v < n+i.val) ∧
    (∀ opGate ∈ C.gates, opGate.inputs.length ≤ 2 ∧
      (opGate.op = .and ∨ opGate.op = .or ∨ opGate.op = .mod 2 ∨
        (opGate.op = .not ∧ opGate.inputs.length = 1)))
  let cost := fun (C : Circ) => C.gates.countP (fun gate => @decide
    ((gate.op = .and ∨ gate.op = .or) ∧ gate.inputs.length = 2) (Classical.propDecidable _))
  let universal := fun (g : Nat) =>
    ∀ (k : Nat) (truth : W → Fin k → Bool) (w : W → Fin k → ℚ) (D : Fin k → Finset W),
      (∀ x y, 0 ≤ w x y) → (∀ y, 16*(∑ x : W, (w x y)^2) ≤ (H : ℚ)) →
      ∃ (z : Nat) (C : Fin z → Circ) (tap : Fin z → Fin (h+1) → Nat)
        (read : Fin z → (Fin (h+1) → Bool) → Fin k → Bool),
        0 < z ∧ (∀ s, legal (C s) ∧ cost (C s) ≤ g ∧ ∀ j, tap s j < n+(C s).gates.length) ∧
        ∀ x y,
          let reward : ℚ := if x ∈ D y then 1 else min (w x y) (1/2)
          let hits := ((Finset.univ : Finset (Fin z)).filter (fun s =>
            read s (fun j => ((C s).wires (List.ofFn x)).getD (tap s j) false) y = truth x y)).card
          (1+reward-2*((D y).card : ℚ)/(H : ℚ))*(z : ℚ) ≤ 2*(hits : ℚ)
  universal (t/2) ∧ ∀ g : Nat, universal g → t/2 ≤ g+3) := by
  intro n h hle
  exact ⟨PEqualNP.Outside.L_lib_1044_aux.upper n h hle, fun g hg => PEqualNP.Outside.L_lib_1044_aux.converse hle hg⟩
