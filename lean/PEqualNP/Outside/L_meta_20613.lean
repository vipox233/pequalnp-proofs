import Mathlib.Tactic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20613

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def W (gs : List Gate) (x : List Bool) : List Bool := gs.foldl stp x

def Good (g : Gate) : Prop := (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

theorem W_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    W (gs ++ [g]) x = stp (W gs x) g := by simp [W]

theorem W_len (gs : List Gate) (x : List Bool) : (W gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [W]
  | append_singleton gs g ih => rw [W_snoc, stp]; simp [ih]; omega

theorem getD_lt (l : List Bool) (b : Bool) (i : ℕ) (h : i < l.length) :
    (l ++ [b]).getD i false = l.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_len (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_big (l : List Bool) (i : ℕ) (h : l.length ≤ i) : l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

def lf (i : ℕ) : ℕ := [31, 992, 31744, 1015808, 32505856, 1082401, 2164802, 4329604, 8659208, 17318416].getD i 0

def X (p : ℕ) : List Bool :=
  oneEach (⟨p / 5 % 5, by omega⟩ : Fin 5) (⟨p % 5, by omega⟩ : Fin 5)

theorem X_len (p : ℕ) : (X p).length = 10 := by simp [X, oneEach]

theorem lf_X : ∀ i < 10, ∀ p < 25, (lf i).testBit p = (X p).getD i false := by decide +kernel

def ev (gs : List Gate) (g : Gate) (x : List Bool) : Bool :=
  g.op.eval (g.inputs.map fun i => (W gs x).getD i false)

def Irr (gs : List Gate) : Prop := ∀ pre g post, gs = pre ++ g :: post →
  (∀ a < 10 + pre.length, ¬ ∀ p < 25, ev pre g (X p) = (W pre (X p)).getD a false) ∧
  ¬ ∀ p < 25, ev pre g (X p) = false

theorem Irr_prefix (gs : List Gate) (g : Gate) (h : Irr (gs ++ [g])) : Irr gs := by
  intro pre g' post e
  exact h pre g' (post ++ [g]) (by rw [e]; simp)

def rho (k a i : ℕ) : ℕ := if i < k then i else if i = k then a else i - 1

def ren (k a : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (rho k a)⟩

theorem ren_wires (pre : List Gate) (g : Gate) (x : List Bool) (hx : x.length = 10) (a L : ℕ)
    (ha : (a < 10 + pre.length ∧ ev pre g x = (W pre x).getD a false) ∨
      (a = 10 + pre.length + L ∧ ev pre g x = false)) (post : List Gate) : post.length ≤ L →
    ∀ i, (W (pre ++ post.map (ren (10 + pre.length) a)) x).getD (rho (10 + pre.length) a i) false =
      (W (pre ++ g :: post) x).getD i false := by
  set k := 10 + pre.length with hk
  induction post using List.reverseRecOn with
  | nil =>
    intro _ i
    have h1 : W (pre ++ [g]) x = W pre x ++ [ev pre g x] := by rw [W_snoc]; rfl
    have hl : (W pre x).length = k := by rw [W_len, hx]
    simp only [List.map_nil, List.append_nil]
    rw [h1]
    rcases lt_trichotomy i k with h | h | h
    · rw [rho, ite_eq_left h, getD_lt _ _ _ (by omega)]
    · rw [rho, ite_eq_right (by omega), ite_eq_left h]
      have h2 := getD_len (W pre x) (ev pre g x)
      rw [hl] at h2
      rw [h, h2]
      rcases ha with ⟨_, h3⟩ | ⟨h3, h4⟩
      · exact h3.symm
      · rw [h4, getD_big _ _ (by omega)]
    · rw [rho, ite_eq_right (by omega), ite_eq_right (by omega), getD_big _ _ (by omega),
        getD_big _ _ (by simp; omega)]
  | append_singleton post h ih =>
    intro hL i
    simp only [List.length_append, List.length_singleton] at hL
    have IH := ih (by omega)
    set w0 := W (pre ++ g :: post) x with hw0
    set w1 := W (pre ++ post.map (ren k a)) x with hw1
    have l0 : w0.length = k + 1 + post.length := by rw [hw0, W_len, hx]; simp; omega
    have l1 : w1.length = k + post.length := by rw [hw1, W_len, hx]; simp; omega
    have e0 : W (pre ++ g :: (post ++ [h])) x = w0 ++ [ev (pre ++ g :: post) h x] := by
      rw [show pre ++ g :: (post ++ [h]) = (pre ++ g :: post) ++ [h] by simp, W_snoc]; rfl
    have e1 : W (pre ++ (post ++ [h]).map (ren k a)) x =
        w1 ++ [ev (pre ++ post.map (ren k a)) (ren k a h) x] := by
      rw [show pre ++ (post ++ [h]).map (ren k a) =
        (pre ++ post.map (ren k a)) ++ [ren k a h] by simp, W_snoc]; rfl
    have ee : ev (pre ++ post.map (ren k a)) (ren k a h) x = ev (pre ++ g :: post) h x := by
      unfold ev ren
      simp only [List.map_map]
      congr 1
      apply List.map_congr_left
      intro j _
      exact IH j
    rw [e0, e1, ee]
    rcases lt_trichotomy i w0.length with hi | hi | hi
    · rw [getD_lt _ _ _ hi, ← IH i]
      rcases lt_trichotomy i k with h' | h' | h'
      · rw [rho, ite_eq_left h', getD_lt _ _ _ (by omega)]
      · rw [rho, ite_eq_right (by omega), ite_eq_left h']
        rcases ha with ⟨h3, _⟩ | ⟨h3, _⟩
        · rw [getD_lt _ _ _ (by omega)]
        · rw [getD_big _ _ (by simp; omega), getD_big _ _ (by omega)]
      · rw [rho, ite_eq_right (by omega), ite_eq_right (by omega), getD_lt _ _ _ (by omega)]
    · have h2 := getD_len w0 (ev (pre ++ g :: post) h x)
      rw [hi, h2, rho, ite_eq_right (by omega), ite_eq_right (by omega)]
      have h3 := getD_len w1 (ev (pre ++ g :: post) h x)
      rw [show w0.length - 1 = w1.length by omega, h3]
    · rw [rho, ite_eq_right (by omega), ite_eq_right (by omega), getD_big _ _ (by simp; omega),
        getD_big _ _ (by simp; omega)]

theorem min_circ (A : Fin 5 → Fin 5 → Bool) (s : ℕ) (h : RepSizeAtMost A s) :
    ∃ C : Circuit, (∀ g ∈ C.gates, Good g) ∧ C.gates.length ≤ s ∧ Represents A C ∧ Irr C.gates := by
  classical
  have hex : ∃ t, ∃ C : Circuit, (∀ g ∈ C.gates, Good g) ∧ C.gates.length = t ∧ Represents A C := by
    obtain ⟨C, hC, _, hr⟩ := h
    exact ⟨_, C, fun g hg => by simpa [Good] using hC g hg, rfl, hr⟩
  obtain ⟨C, hC, hlen, hrep⟩ := Nat.find_spec hex
  have hle : C.gates.length ≤ s := by
    obtain ⟨C', hC', hs, hr⟩ := h
    rw [hlen]
    exact (Nat.find_min' hex ⟨C', fun g hg => by simpa [Good] using hC' g hg, rfl, hr⟩).trans hs
  refine ⟨C, hC, hle, hrep, ?_⟩

  have key : ∀ pre g post, C.gates = pre ++ g :: post → ∀ a,
      (∀ p < 25, (a < 10 + pre.length ∧ ev pre g (X p) = (W pre (X p)).getD a false) ∨
        (a = 10 + pre.length + post.length ∧ ev pre g (X p) = false)) → False := by
    intro pre g post e a ha
    have hnew : ∃ C' : Circuit, (∀ g ∈ C'.gates, Good g) ∧
        C'.gates.length = C.gates.length - 1 ∧ Represents A C' := by
      refine ⟨⟨pre ++ post.map (ren (10 + pre.length) a), rho (10 + pre.length) a C.output⟩,
        ?_, ?_, ?_⟩
      · intro g' hg'
        rcases List.mem_append.mp hg' with h1 | h1
        · exact hC g' (by rw [e]; simp [h1])
        · obtain ⟨h2, h3, rfl⟩ := List.mem_map.mp h1
          have := hC h2 (by rw [e]; simp [h3])
          exact ⟨this.1, by simpa [ren] using this.2⟩
      · rw [e]; simp
      · intro u v
        have hp : 5 * (u : ℕ) + v < 25 := by omega
        have hX : X (5 * (u : ℕ) + v) = oneEach u v := by
          unfold X
          congr 1 <;> apply Fin.ext <;> simp <;> omega
        have h1 := ren_wires pre g (X (5 * (u : ℕ) + v)) (X_len _) a post.length (ha _ hp) post
          le_rfl C.output
        rw [← e, hX] at h1
        exact h1.trans (hrep u v)
    have := Nat.find_min' hex hnew
    have hpos : 0 < C.gates.length := by rw [e]; simp
    omega
  intro pre g post e
  refine ⟨fun a ha hall => key pre g post e a (fun p hp => Or.inl ⟨ha, hall p hp⟩),
    fun hall => key pre g post e _ (fun p hp => Or.inr ⟨rfl, hall p hp⟩)⟩

def MM : ℕ := 12979296

def FULL : ℕ := 2 ^ 25 - 1

def RO (ng : Bool) (lv : ℕ → ℕ) (K S m : ℕ) : Prop :=
  ∀ Q : ℕ → ℕ → Prop, (∀ i < K, Q (2 ^ i) (lv i)) →
    (∀ A B a b, (∀ i, A.testBit i = true → B.testBit i = false) → Q A a → Q B b →
      Q (A ||| B) (a &&& b) ∧ Q (A ||| B) (a ||| b)) →
    (ng = true → ∀ A a, Q A a → Q A (FULL ^^^ a)) → Q S m

theorem RO_leaf (ng : Bool) (lv : ℕ → ℕ) (K i : ℕ) (h : i < K) : RO ng lv K (2 ^ i) (lv i) :=
  fun _ h1 _ _ => h1 i h

theorem RO_and {ng : Bool} {lv : ℕ → ℕ} {K A B a b : ℕ}
    (h : ∀ i, A.testBit i = true → B.testBit i = false)
    (ha : RO ng lv K A a) (hb : RO ng lv K B b) : RO ng lv K (A ||| B) (a &&& b) :=
  fun Q h1 h2 h3 => (h2 A B a b h (ha Q h1 h2 h3) (hb Q h1 h2 h3)).1

theorem RO_or {ng : Bool} {lv : ℕ → ℕ} {K A B a b : ℕ}
    (h : ∀ i, A.testBit i = true → B.testBit i = false)
    (ha : RO ng lv K A a) (hb : RO ng lv K B b) : RO ng lv K (A ||| B) (a ||| b) :=
  fun Q h1 h2 h3 => (h2 A B a b h (ha Q h1 h2 h3) (hb Q h1 h2 h3)).2

theorem RO_not {lv : ℕ → ℕ} {K A a : ℕ} (ha : RO true lv K A a) : RO true lv K A (FULL ^^^ a) :=
  fun Q h1 h2 h3 => h3 rfl A a (ha Q h1 h2 h3)

theorem RO_true {ng : Bool} {lv : ℕ → ℕ} {K A a : ℕ} (ha : RO ng lv K A a) : RO true lv K A a :=
  fun Q h1 h2 h3 => ha Q h1 h2 (fun _ => h3 rfl)

theorem FULL_bit (p : ℕ) (hp : p < 25) (m : ℕ) : (FULL ^^^ m).testBit p = !m.testBit p := by
  rw [Nat.testBit_xor]
  have : FULL.testBit p = true := by
    unfold FULL; rw [Nat.testBit_two_pow_sub_one]; simpa using hp
  rw [this]; simp

def ext (lv : ℕ → ℕ) (K z i : ℕ) : ℕ := if i < K then lv i else z

theorem RO_lift (ng : Bool) (lv : ℕ → ℕ) (K z S m : ℕ) (h : RO ng lv K S m) :
    RO ng (ext lv K z) (K + 2) S m := by
  intro Q h1 h2 h3
  refine h Q (fun i hi => ?_) h2 h3
  have := h1 i (by omega)
  simpa [ext, hi] using this

def Fam (ng : Bool) (lv : ℕ → ℕ) (K : ℕ) (D : ℕ → Prop) (I : Finset ℕ) (val : ℕ → ℕ → Bool) : Prop :=
  ∃ S m : ℕ → ℕ, (∀ w ∈ I, RO ng lv K (S w) (m w)) ∧
    (∀ w ∈ I, ∀ p < 25, (m w).testBit p = val w p) ∧
    (∀ w ∈ I, ∀ w' ∈ I, w ≠ w' → ∀ i, (S w).testBit i = true → (S w').testBit i = false) ∧
    (∀ i, (∃ w ∈ I, (S w).testBit i = true) ↔ D i)

def Sh (ng : Bool) : ℕ → (ℕ → ℕ) → ℕ → (ℕ → Prop) → Finset ℕ → (ℕ → ℕ → Bool) → Prop
  | 0, lv, K, D, I, val => Fam ng lv K D I val
  | j + 1, lv, K, D, I, val => ∃ Sc mc : ℕ, RO ng lv K Sc mc ∧ (∀ i, Sc.testBit i = true → D i) ∧
      Sh ng j (ext lv K mc) (K + 2) (fun i => (D i ∧ Sc.testBit i = false) ∨ i = K ∨ i = K + 1) I val

theorem Sh_map (ng : Bool) (I I' : Finset ℕ) (val val' : ℕ → ℕ → Bool)
    (h : ∀ lv K D, Fam ng lv K D I val → Fam ng lv K D I' val') :
    ∀ j lv K D, Sh ng j lv K D I val → Sh ng j lv K D I' val' := by
  intro j
  induction j with
  | zero => exact h
  | succ j ih =>
    rintro lv K D ⟨Sc, mc, h1, h2, h3⟩
    exact ⟨Sc, mc, h1, h2, ih _ _ _ h3⟩

theorem Fam_true (ng : Bool) (lv : ℕ → ℕ) (K : ℕ) (D : ℕ → Prop) (I : Finset ℕ)
    (val : ℕ → ℕ → Bool) (h : Fam ng lv K D I val) : Fam true lv K D I val := by
  obtain ⟨S, m, h1, h2⟩ := h
  exact ⟨S, m, fun w hw => RO_true (h1 w hw), h2⟩

theorem Sh_true (ng : Bool) (I : Finset ℕ) (val : ℕ → ℕ → Bool) :
    ∀ j lv K D, Sh ng j lv K D I val → Sh true j lv K D I val := by
  intro j
  induction j with
  | zero => exact fun lv K D h => Fam_true ng lv K D I val h
  | succ j ih =>
    rintro lv K D ⟨Sc, mc, h1, h2, h3⟩
    exact ⟨Sc, mc, RO_true h1, h2, ih _ _ _ h3⟩

theorem Fam_not (I : Finset ℕ) (val : ℕ → ℕ → Bool) (a e : ℕ) (ha : a ∈ I) (he : e ∉ I.erase a)
    (hv : ∀ p < 25, val e p = !val a p) (lv : ℕ → ℕ) (K : ℕ) (D : ℕ → Prop)
    (hF : Fam true lv K D I val) : Fam true lv K D (insert e (I.erase a)) val := by
  obtain ⟨S, m, hRO, hval, hdis, hun⟩ := hF
  have hR : ∀ w ∈ I.erase a, w ≠ e ∧ w ≠ a ∧ w ∈ I := by
    intro w hw
    have h1 := Finset.mem_erase.mp hw
    exact ⟨fun h => he (h ▸ hw), h1.1, h1.2⟩
  refine ⟨fun w => if w = e then S a else S w, fun w => if w = e then FULL ^^^ m a else m w,
    ?_, ?_, ?_, ?_⟩
  · intro w hw
    rcases Finset.mem_insert.mp hw with h | h
    · simp only [h, ↓reduceIte]; exact RO_not (hRO a ha)
    · simp only [(hR w h).1, ↓reduceIte]; exact hRO w (hR w h).2.2
  · intro w hw p hp
    rcases Finset.mem_insert.mp hw with h | h
    · simp only [h, ↓reduceIte]
      rw [FULL_bit p hp, hval a ha p hp, hv p hp]
    · simp only [(hR w h).1, ↓reduceIte]; exact hval w (hR w h).2.2 p hp
  · intro w hw w' hw' hww i hi
    rcases Finset.mem_insert.mp hw with h | h
    · rcases Finset.mem_insert.mp hw' with h' | h'
      · exact absurd (h.trans h'.symm) hww
      · obtain ⟨e1, e2, e3⟩ := hR w' h'
        simp only [h, ↓reduceIte] at hi
        simp only [e1, ↓reduceIte]
        exact hdis a ha w' e3 e2.symm i hi
    · obtain ⟨e1, e2, e3⟩ := hR w h
      simp only [e1, ↓reduceIte] at hi
      rcases Finset.mem_insert.mp hw' with h' | h'
      · simp only [h', ↓reduceIte]
        exact hdis w e3 a ha e2 i hi
      · obtain ⟨e1', e2', e3'⟩ := hR w' h'
        simp only [e1', ↓reduceIte]
        exact hdis w e3 w' e3' hww i hi
  · intro i
    rw [← hun i]
    constructor
    · rintro ⟨w, hw, hb'⟩
      rcases Finset.mem_insert.mp hw with h | h
      · simp only [h, ↓reduceIte] at hb'
        exact ⟨a, ha, hb'⟩
      · simp only [(hR w h).1, ↓reduceIte] at hb'
        exact ⟨w, (hR w h).2.2, hb'⟩
    · rintro ⟨w, hw, hb'⟩
      by_cases h1 : w = a
      · refine ⟨e, Finset.mem_insert_self _ _, ?_⟩
        simp only [↓reduceIte]; rw [← h1]; exact hb'
      · have hw' : w ∈ I.erase a := Finset.mem_erase.mpr ⟨h1, hw⟩
        refine ⟨w, Finset.mem_insert_of_mem hw', ?_⟩
        simp only [(hR w hw').1, ↓reduceIte]; exact hb'

theorem Fam_congr (ng : Bool) (I : Finset ℕ) (val val' : ℕ → ℕ → Bool)
    (h : ∀ w ∈ I, ∀ p < 25, val w p = val' w p) (lv : ℕ → ℕ) (K : ℕ) (D : ℕ → Prop)
    (hF : Fam ng lv K D I val) : Fam ng lv K D I val' := by
  obtain ⟨S, m, h1, h2, h3, h4⟩ := hF
  exact ⟨S, m, h1, fun w hw p hp => by rw [h2 w hw p hp, h w hw p hp], h3, h4⟩

theorem Fam_bin (ng : Bool) (I : Finset ℕ) (val : ℕ → ℕ → Bool) (a b e : ℕ) (ha : a ∈ I) (hb : b ∈ I)
    (hab : a ≠ b) (he : e ∉ (I.erase a).erase b)
    (hv : (∀ p < 25, val e p = (val a p && val b p)) ∨ (∀ p < 25, val e p = (val a p || val b p)))
    (lv : ℕ → ℕ) (K : ℕ) (D : ℕ → Prop) (hF : Fam ng lv K D I val) :
    Fam ng lv K D (insert e ((I.erase a).erase b)) val := by
  obtain ⟨S, m, hRO, hval, hdis, hun⟩ := hF
  have hSab := hdis a ha b hb hab
  obtain ⟨mk, hmk1, hmk2⟩ : ∃ mk, RO ng lv K (S a ||| S b) mk ∧ ∀ p < 25,
      mk.testBit p = val e p := by
    rcases hv with hv | hv
    · exact ⟨_, RO_and hSab (hRO a ha) (hRO b hb), fun p hp => by
        rw [hv p hp, Nat.testBit_and, hval a ha p hp, hval b hb p hp]⟩
    · exact ⟨_, RO_or hSab (hRO a ha) (hRO b hb), fun p hp => by
        rw [hv p hp, Nat.testBit_or, hval a ha p hp, hval b hb p hp]⟩
  have hR : ∀ w ∈ (I.erase a).erase b, w ≠ e ∧ w ≠ a ∧ w ≠ b ∧ w ∈ I := by
    intro w hw
    have h1 := Finset.mem_erase.mp hw
    have h2 := Finset.mem_erase.mp h1.2
    exact ⟨fun h => he (h ▸ hw), h2.1, h1.1, h2.2⟩
  refine ⟨fun w => if w = e then S a ||| S b else S w, fun w => if w = e then mk else m w,
    ?_, ?_, ?_, ?_⟩
  · intro w hw
    rcases Finset.mem_insert.mp hw with h | h
    · simp only [h, ↓reduceIte]; exact hmk1
    · simp only [(hR w h).1, ↓reduceIte]; exact hRO w (hR w h).2.2.2
  · intro w hw p hp
    rcases Finset.mem_insert.mp hw with h | h
    · simp only [h, ↓reduceIte]; exact hmk2 p hp
    · simp only [(hR w h).1, ↓reduceIte]; exact hval w (hR w h).2.2.2 p hp
  · intro w hw w' hw' hww i hi
    rcases Finset.mem_insert.mp hw with h | h
    · rcases Finset.mem_insert.mp hw' with h' | h'
      · exact absurd (h.trans h'.symm) hww
      · obtain ⟨e1, e2, e3, e4⟩ := hR w' h'
        simp only [h, ↓reduceIte, Nat.testBit_or, Bool.or_eq_true] at hi
        simp only [e1, ↓reduceIte]
        rcases hi with hi | hi
        · exact hdis a ha w' e4 e2.symm i hi
        · exact hdis b hb w' e4 e3.symm i hi
    · obtain ⟨e1, e2, e3, e4⟩ := hR w h
      simp only [e1, ↓reduceIte] at hi
      rcases Finset.mem_insert.mp hw' with h' | h'
      · simp only [h', ↓reduceIte, Nat.testBit_or, Bool.or_eq_false_iff]
        exact ⟨hdis w e4 a ha e2 i hi, hdis w e4 b hb e3 i hi⟩
      · obtain ⟨e1', e2', e3', e4'⟩ := hR w' h'
        simp only [e1', ↓reduceIte]
        exact hdis w e4 w' e4' hww i hi
  · intro i
    rw [← hun i]
    constructor
    · rintro ⟨w, hw, hb'⟩
      rcases Finset.mem_insert.mp hw with h | h
      · simp only [h, ↓reduceIte, Nat.testBit_or, Bool.or_eq_true] at hb'
        rcases hb' with hb' | hb'
        · exact ⟨a, ha, hb'⟩
        · exact ⟨b, hb, hb'⟩
      · simp only [(hR w h).1, ↓reduceIte] at hb'
        exact ⟨w, (hR w h).2.2.2, hb'⟩
    · rintro ⟨w, hw, hb'⟩
      by_cases h1 : w = a ∨ w = b
      · refine ⟨e, Finset.mem_insert_self _ _, ?_⟩
        simp only [↓reduceIte, Nat.testBit_or, Bool.or_eq_true]
        rcases h1 with rfl | rfl
        · exact Or.inl hb'
        · exact Or.inr hb'
      · rw [not_or] at h1
        have hw' : w ∈ (I.erase a).erase b :=
          Finset.mem_erase.mpr ⟨h1.2, Finset.mem_erase.mpr ⟨h1.1, hw⟩⟩
        refine ⟨w, Finset.mem_insert_of_mem hw', ?_⟩
        simp only [(hR w hw').1, ↓reduceIte]; exact hb'

theorem Fam_dup (ng : Bool) (I : Finset ℕ) (val : ℕ → ℕ → Bool) (a e : ℕ) (ha : a ∈ I) (he : e ∉ I)
    (hv : ∀ p < 25, val e p = val a p) (lv : ℕ → ℕ) (K : ℕ) (D : ℕ → Prop)
    (hDK : ∀ i, D i → i < K) (hF : Fam ng lv K D I val) : Sh ng 1 lv K D (insert e I) val := by
  obtain ⟨S, m, hRO, hval, hdis, hun⟩ := hF
  have hlt : ∀ w ∈ I, ∀ i, (S w).testBit i = true → i < K := fun w hw i hi =>
    hDK i ((hun i).mp ⟨w, hw, hi⟩)
  refine ⟨S a, m a, hRO a ha, fun i hi => (hun i).mp ⟨a, ha, hi⟩, ?_⟩
  have hRK : RO ng (ext lv K (m a)) (K + 2) (2 ^ K) (m a) := by
    have := RO_leaf ng (ext lv K (m a)) (K + 2) K (by omega)
    simpa [ext] using this
  have hRK1 : RO ng (ext lv K (m a)) (K + 2) (2 ^ (K + 1)) (m a) := by
    have := RO_leaf ng (ext lv K (m a)) (K + 2) (K + 1) (by omega)
    simpa [ext] using this
  have hb0 : ∀ i, (2 ^ K : ℕ).testBit i = true ↔ i = K := by
    intro i; rw [Nat.testBit_two_pow]; simp [eq_comm]
  have hb1 : ∀ i, (2 ^ (K + 1) : ℕ).testBit i = true ↔ i = K + 1 := by
    intro i; rw [Nat.testBit_two_pow]; simp [eq_comm]
  have hea : e ≠ a := fun h => he (h ▸ ha)
  set SS : ℕ → ℕ := fun w => if w = e then 2 ^ (K + 1) else if w = a then 2 ^ K else S w with hSS
  have eE : SS e = 2 ^ (K + 1) := by simp [hSS]
  have eA : SS a = 2 ^ K := by simp [hSS, hea.symm]
  have eO : ∀ w, w ≠ e → w ≠ a → SS w = S w := fun w h1 h2 => by simp [hSS, h1, h2]
  have key : ∀ w ∈ insert e I, ∀ i, (SS w).testBit i = true →
      (w = e ∧ i = K + 1) ∨ (w = a ∧ i = K) ∨ (w ≠ e ∧ w ≠ a ∧ w ∈ I ∧ (S w).testBit i = true) := by
    intro w hw i hi
    by_cases h1 : w = e
    · rw [h1, eE, hb1] at hi; exact Or.inl ⟨h1, hi⟩
    · by_cases h2 : w = a
      · rw [h2, eA, hb0] at hi; exact Or.inr (Or.inl ⟨h2, hi⟩)
      · rw [eO w h1 h2] at hi
        exact Or.inr (Or.inr ⟨h1, h2, (Finset.mem_insert.mp hw).resolve_left h1, hi⟩)
  refine ⟨SS, fun w => if w = e then m a else m w, ?_, ?_, ?_, ?_⟩
  · intro w hw
    by_cases h1 : w = e
    · rw [h1, eE]; simp only [↓reduceIte]; exact hRK1
    · simp only [h1, ↓reduceIte]
      by_cases h2 : w = a
      · rw [h2, eA]; exact hRK
      · rw [eO w h1 h2]
        exact RO_lift _ _ _ _ _ _ (hRO w ((Finset.mem_insert.mp hw).resolve_left h1))
  · intro w hw p hp
    by_cases h1 : w = e
    · simp only [h1, ↓reduceIte]; rw [hv p hp]; exact hval a ha p hp
    · simp only [h1, ↓reduceIte]
      exact hval w ((Finset.mem_insert.mp hw).resolve_left h1) p hp
  · intro w hw w' hw' hww i hi
    by_contra hne
    have k1 := key w hw i hi
    have k2 := key w' hw' i (by simpa using hne)
    rcases k1 with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2, e3, e4⟩
    · rcases k2 with ⟨f1, f2⟩ | ⟨f1, f2⟩ | ⟨f1, f2, f3, f4⟩
      · exact hww (e1.trans f1.symm)
      · omega
      · have := hlt w' f3 i f4; omega
    · rcases k2 with ⟨f1, f2⟩ | ⟨f1, f2⟩ | ⟨f1, f2, f3, f4⟩
      · omega
      · exact hww (e1.trans f1.symm)
      · have := hlt w' f3 i f4; omega
    · rcases k2 with ⟨f1, f2⟩ | ⟨f1, f2⟩ | ⟨f1, f2, f3, f4⟩
      · have := hlt w e3 i e4; omega
      · have := hlt w e3 i e4; omega
      · have := hdis w e3 w' f3 hww i e4
        rw [this] at f4; exact absurd f4 (by simp)
  · intro i
    constructor
    · rintro ⟨w, hw, hi⟩
      rcases key w hw i hi with ⟨_, e2⟩ | ⟨_, e2⟩ | ⟨e1, e2, e3, e4⟩
      · exact Or.inr (Or.inr e2)
      · exact Or.inr (Or.inl e2)
      · exact Or.inl ⟨(hun i).mp ⟨w, e3, e4⟩, hdis w e3 a ha e2 i e4⟩
    · rintro (⟨hiD, hia⟩ | rfl | rfl)
      · obtain ⟨w, hw, hi⟩ := (hun i).mpr hiD
        have h2 : w ≠ a := by
          rintro rfl; rw [hi] at hia; exact absurd hia (by simp)
        have h1 : w ≠ e := fun h => he (h ▸ hw)
        exact ⟨w, Finset.mem_insert_of_mem hw, by rw [eO w h1 h2]; exact hi⟩
      · exact ⟨a, Finset.mem_insert_of_mem ha, by rw [eA, hb0]⟩
      · exact ⟨e, Finset.mem_insert_self _ _, by rw [eE, hb1]⟩

theorem Sh_dup (ng : Bool) (I : Finset ℕ) (val : ℕ → ℕ → Bool) (a e : ℕ) (ha : a ∈ I) (he : e ∉ I)
    (hv : ∀ p < 25, val e p = val a p) : ∀ j lv K (D : ℕ → Prop), (∀ i, D i → i < K) →
    Sh ng j lv K D I val → Sh ng (j + 1) lv K D (insert e I) val := by
  intro j
  induction j with
  | zero => intro lv K D hDK h; exact Fam_dup ng I val a e ha he hv lv K D hDK h
  | succ j ih =>
    rintro lv K D hDK ⟨Sc, mc, h1, h2, h3⟩
    refine ⟨Sc, mc, h1, h2, ih _ _ _ ?_ h3⟩
    rintro i (⟨h, _⟩ | h | h)
    · have := hDK i h; omega
    · omega
    · omega

def Det (gs : List Gate) (pend D : Finset ℕ) : Prop :=
  ∀ x y : List Bool, x.length = 10 → y.length = 10 →
    (∀ i ∈ D, x.getD i false = y.getD i false) →
    ∀ w ∈ pend, (W gs x).getD w false = (W gs y).getD w false

def vl (gs : List Gate) (w p : ℕ) : Bool := (W gs (X p)).getD w false

theorem main (gs : List Gate) : (∀ g ∈ gs, Good g) → Irr gs → ∀ pend : Finset ℕ,
    (∀ w ∈ pend, w < 10 + gs.length) → (∀ w ∈ pend, ∃ p < 25, vl gs w p = false) →
    ∃ D : Finset ℕ, D ⊆ Finset.range 10 ∧ Det gs pend D ∧
      ∃ j, D.card + j ≤ pend.card + gs.length ∧ Sh false j lf 10 (· ∈ D) pend (vl gs) := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro _ _ pend hp _
    refine ⟨pend, fun w hw => by simpa using hp w hw, fun x y _ _ h w hw => by
      simpa [W] using h w hw, 0, by simp, fun w => 2 ^ w, lf,
      fun w hw => RO_leaf false lf 10 w (by simpa using hp w hw),
      fun w hw p hpp => by simpa [W, vl] using lf_X w (by simpa using hp w hw) p hpp,
      fun w hw w' hw' hne i hi => ?_, fun i => ?_⟩
    · rw [Nat.testBit_two_pow] at hi ⊢
      have : w = i := by simpa using hi
      simp only [decide_eq_false_iff_not]
      omega
    · simp [Nat.testBit_two_pow]
  | append_singleton gs g ih =>
    intro hg hirr pend hp hnt
    have hg' : ∀ g ∈ gs, Good g := fun g' h => hg g' (by simp [h])
    have hgg : Good g := hg g (by simp)
    have hlen : (gs ++ [g]).length = gs.length + 1 := by simp
    have IH := ih hg' (Irr_prefix gs g hirr)
    have hI := hirr gs g [] rfl
    set k := 10 + gs.length with hk
    have hlo : ∀ x : List Bool, x.length = 10 → ∀ w, w < k →
        (W (gs ++ [g]) x).getD w false = (W gs x).getD w false := by
      intro x hx w hw
      rw [W_snoc, stp, getD_lt _ _ _ (by rw [W_len, hx]; exact hw)]
    have hto : ∀ x : List Bool, x.length = 10 →
        (W (gs ++ [g]) x).getD k false = ev gs g x := by
      intro x hx
      have h := getD_len (W gs x) (ev gs g x)
      rw [W_len, hx] at h
      rw [W_snoc]; exact h
    have hvlo : ∀ w, w < k → ∀ p, vl (gs ++ [g]) w p = vl gs w p := fun w hw p =>
      hlo _ (X_len p) w hw
    have hvto : ∀ p, vl (gs ++ [g]) k p = ev gs g (X p) := fun p => hto _ (X_len p)
    have hpk : ∀ w ∈ pend, w ≠ k → w < k := by
      intro w hw hwk
      have h1 := hp w hw
      rw [hlen] at h1; omega
    have hbig : ∀ x : List Bool, x.length = 10 → ∀ i, k ≤ i → (W gs x).getD i false = false := by
      intro x hx i hi
      exact getD_big _ _ (by rw [W_len, hx]; omega)
    by_cases hkp : k ∈ pend
    swap
    · have hp' : ∀ w ∈ pend, w < k := fun w hw => hpk w hw (fun h => hkp (h ▸ hw))
      obtain ⟨D, h1, h2, j, h3, h4⟩ := IH pend hp' (fun w hw => by
        obtain ⟨p, hpp, h⟩ := hnt w hw
        exact ⟨p, hpp, by rw [← hvlo w (hp' w hw) p]; exact h⟩)
      refine ⟨D, h1, ?_, j, by rw [hlen]; omega, ?_⟩
      · intro x y hx hy hxy w hw
        rw [hlo x hx w (hp' w hw), hlo y hy w (hp' w hw)]
        exact h2 x y hx hy hxy w hw
      · exact Sh_map false _ _ _ _ (Fam_congr false pend _ _ fun w hw p _ => (hvlo w (hp' w hw) p).symm)
          _ _ _ _ h4
    ·
      obtain ⟨a, b, hak, hbk, hab, hev⟩ : ∃ a b, a < k ∧ b < k ∧ a ≠ b ∧
          ((∀ x : List Bool, x.length = 10 → ev gs g x = ((W gs x).getD a false && (W gs x).getD b false)) ∨
           (∀ x : List Bool, x.length = 10 → ev gs g x = ((W gs x).getD a false || (W gs x).getD b false))) := by
        have hcopy : ∀ a < k, (∀ x : List Bool, x.length = 10 → ev gs g x = (W gs x).getD a false) →
            False := fun a ha h => hI.1 a ha (fun p _ => h _ (X_len p))
        have hfalse : (∀ x : List Bool, x.length = 10 → ev gs g x = false) → False :=
          fun h => hI.2 (fun p _ => h _ (X_len p))
        have hl2 := hgg.2
        rcases hins : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨t, l⟩⟩⟩
        · exfalso
          rcases hgg.1 with ho | ho
          · obtain ⟨p, _, h⟩ := hnt k hkp
            rw [hvto p] at h
            simp [ev, hins, ho, GateOp.eval] at h
          · apply hfalse; intro x _
            simp [ev, hins, ho, GateOp.eval]
        · exfalso
          have he : ∀ x, ev gs g x = (W gs x).getD a false := by
            intro x
            rcases hgg.1 with ho | ho <;> simp [ev, hins, ho, GateOp.eval]
          by_cases hak : a < k
          · exact hcopy a hak (fun x _ => he x)
          · exact hfalse (fun x hx => by rw [he x, hbig x hx a (by omega)])
        · rcases hgg.1 with ho | ho
          · have he : ∀ x, ev gs g x = ((W gs x).getD a false && (W gs x).getD b false) := by
              intro x; simp [ev, hins, ho, GateOp.eval]
            by_cases hak : a < k
            · by_cases hbk : b < k
              · by_cases hab : a = b
                · exact (hcopy b hbk fun x _ => by rw [he x, hab, Bool.and_self]).elim
                · exact ⟨a, b, hak, hbk, hab, Or.inl fun x _ => he x⟩
              · exact (hfalse fun x hx => by
                  rw [he x, hbig x hx b (by omega), Bool.and_false]).elim
            · exact (hfalse fun x hx => by
                rw [he x, hbig x hx a (by omega), Bool.false_and]).elim
          · have he : ∀ x, ev gs g x = ((W gs x).getD a false || (W gs x).getD b false) := by
              intro x; simp [ev, hins, ho, GateOp.eval]
            by_cases hak : a < k
            · by_cases hbk : b < k
              · by_cases hab : a = b
                · exact (hcopy b hbk fun x _ => by rw [he x, hab, Bool.or_self]).elim
                · exact ⟨a, b, hak, hbk, hab, Or.inr fun x _ => he x⟩
              · exact (hcopy a hak fun x hx => by
                  rw [he x, hbig x hx b (by omega), Bool.or_false]).elim
            · by_cases hbk : b < k
              · exact (hcopy b hbk fun x hx => by
                  rw [he x, hbig x hx a (by omega), Bool.false_or]).elim
              · exact (hfalse fun x hx => by
                  rw [he x, hbig x hx a (by omega), hbig x hx b (by omega)]; rfl).elim
        · rw [hins] at hl2; simp at hl2

      obtain ⟨p0, hp0, hk0⟩ := hnt k hkp
      rw [hvto p0] at hk0
      have hant : (∃ p < 25, vl gs a p = false) ∧ (∃ p < 25, vl gs b p = false) := by
        rcases hev with hev | hev
        · constructor
          · by_contra hne
            push_neg at hne
            exact hI.1 b hbk fun p hpp => by
              have h1 := hne p hpp
              rw [hev _ (X_len p)]
              have h2 : (W gs (X p)).getD a false = true := by simpa [vl] using h1
              rw [h2, Bool.true_and]
          · by_contra hne
            push_neg at hne
            exact hI.1 a hak fun p hpp => by
              have h1 := hne p hpp
              rw [hev _ (X_len p)]
              have h2 : (W gs (X p)).getD b false = true := by simpa [vl] using h1
              rw [h2, Bool.and_true]
        · rw [hev _ (X_len p0), Bool.or_eq_false_iff] at hk0
          exact ⟨⟨p0, hp0, hk0.1⟩, ⟨p0, hp0, hk0.2⟩⟩
      set E := pend.erase k with hE
      have hEc : E.card + 1 = pend.card := Finset.card_erase_add_one hkp
      have hElt : ∀ w ∈ E, w < k := fun w hw =>
        hpk w (Finset.mem_of_mem_erase hw) (Finset.ne_of_mem_erase hw)
      have hEnt : ∀ w ∈ E, ∃ p < 25, vl gs w p = false := by
        intro w hw
        obtain ⟨p, hpp, h⟩ := hnt w (Finset.mem_of_mem_erase hw)
        exact ⟨p, hpp, by rw [← hvlo w (hElt w hw) p]; exact h⟩
      have hpE : pend = insert k E := (Finset.insert_erase hkp).symm

      have hdet : ∀ (P : Finset ℕ) D, (∀ w ∈ E, w ∈ P) → a ∈ P → b ∈ P → Det gs P D →
          Det (gs ++ [g]) pend D := by
        intro P D hEP haP hbP hD x y hx hy hxy w hw
        by_cases hwk : w = k
        · rw [hwk, hto x hx, hto y hy]
          have h1 := hD x y hx hy hxy a haP
          have h2 := hD x y hx hy hxy b hbP
          rcases hev with hev | hev <;> rw [hev x hx, hev y hy, h1, h2]
        · have hwe : w ∈ E := Finset.mem_erase.mpr ⟨hwk, hw⟩
          rw [hlo x hx w (hElt w hwe), hlo y hy w (hElt w hwe)]
          exact hD x y hx hy hxy w (hEP w hwe)
      set v' : ℕ → ℕ → Bool := fun w p => if w = k + 1 then vl gs a p else
        if w = k + 2 then vl gs b p else vl (gs ++ [g]) w p with hv'
      have v'1 : ∀ p, v' (k + 1) p = vl gs a p := fun p => by simp [hv']
      have v'2 : ∀ p, v' (k + 2) p = vl gs b p := fun p => by simp [hv']
      have v'k : ∀ p, v' k p = ev gs g (X p) := fun p => by
        simp only [hv']
        rw [ite_eq_right (by omega), ite_eq_right (by omega), hvto p]
      have v'l : ∀ w, w < k → ∀ p, v' w p = vl gs w p := fun w hw p => by
        simp only [hv']
        rw [ite_eq_right (by omega), ite_eq_right (by omega), hvlo w hw p]
      have hstart : ∀ (P : Finset ℕ) D j, (∀ w ∈ P, w < k) → Sh false j lf 10 D P (vl gs) →
          Sh false j lf 10 D P v' := fun P D j hP h =>
        Sh_map false _ _ _ _ (Fam_congr false P _ _ fun w hw p _ => (v'l w (hP w hw) p).symm) _ _ _ _ h
      have hend : ∀ D j, Sh false j lf 10 D (insert k E) v' → Sh false j lf 10 D pend (vl (gs ++ [g])) := by
        intro D j h
        rw [hpE]
        refine Sh_map false _ _ _ _ (Fam_congr false _ _ _ fun w hw p _ => ?_) _ _ _ _ h
        rcases Finset.mem_insert.mp hw with rfl | hw
        · rw [v'k, hvto]
        · rw [v'l w (hElt w hw), hvlo w (hElt w hw)]
      have hcomb : ∀ (P : Finset ℕ) D j c d, c ∈ P → d ∈ P → c ≠ d → (P.erase c).erase d = E →
          (∀ p, v' c p = vl gs a p) → (∀ p, v' d p = vl gs b p) → Sh false j lf 10 D P v' →
          Sh false j lf 10 D pend (vl (gs ++ [g])) := by
        intro P D j c d hc hd hcd hPE hvc hvd h
        apply hend
        rw [← hPE]
        refine Sh_map false _ _ _ _ (Fam_bin false P v' c d k hc hd hcd ?_ ?_) _ _ _ _ h
        · rw [hPE]; exact Finset.notMem_erase _ _
        · rcases hev with hev | hev
          · left; intro p _
            rw [v'k, hvc, hvd, hev _ (X_len p)]; rfl
          · right; intro p _
            rw [v'k, hvc, hvd, hev _ (X_len p)]; rfl
      have hD8 : ∀ D : Finset ℕ, D ⊆ Finset.range 10 → ∀ i, i ∈ D → i < 10 := fun D hD i hi => by
        simpa using hD hi
      have hk1E : k + 1 ∉ E := fun h => by have := hElt _ h; omega
      have hk2E : k + 2 ∉ E := fun h => by have := hElt _ h; omega
      by_cases haE : a ∈ E
      · by_cases hbE : b ∈ E
        ·
          obtain ⟨D, h1, h2, j, h3, h4⟩ := IH E hElt hEnt
          refine ⟨D, h1, hdet E D (fun w hw => hw) haE hbE h2, j + 2, by rw [hlen]; omega, ?_⟩
          have s1 := hstart E _ j hElt h4
          have s2 := Sh_dup false E v' a (k + 1) haE hk1E (fun p _ => by rw [v'1, v'l a hak]) j lf 10 _
            (hD8 D h1) s1
          have s3 := Sh_dup false (insert (k + 1) E) v' b (k + 2) (Finset.mem_insert_of_mem hbE)
            (by simp [hk2E]) (fun p _ => by rw [v'2, v'l b hbk]) (j + 1) lf 10 _ (hD8 D h1) s2
          refine hcomb (insert (k + 2) (insert (k + 1) E)) _ _ (k + 1) (k + 2) (by simp) (by simp)
            (by omega) ?_ v'1 v'2 s3
          ext w
          simp only [Finset.mem_erase, Finset.mem_insert]
          constructor
          · rintro ⟨n2, n1, h | h | h⟩
            · exact absurd h n2
            · exact absurd h n1
            · exact h
          · intro h
            have := hElt w h
            exact ⟨by omega, by omega, Or.inr (Or.inr h)⟩
        ·
          have hP : ∀ w ∈ insert b E, w < k := by
            intro w hw
            rcases Finset.mem_insert.mp hw with rfl | hw
            · exact hbk
            · exact hElt w hw
          obtain ⟨D, h1, h2, j, h3, h4⟩ := IH (insert b E) hP (by
            intro w hw
            rcases Finset.mem_insert.mp hw with rfl | hw
            · exact hant.2
            · exact hEnt w hw)
          rw [Finset.card_insert_of_notMem hbE] at h3
          refine ⟨D, h1, hdet (insert b E) D (fun w hw => Finset.mem_insert_of_mem hw)
            (Finset.mem_insert_of_mem haE) (Finset.mem_insert_self _ _) h2, j + 1,
            by rw [hlen]; omega, ?_⟩
          have s1 := hstart (insert b E) _ j hP h4
          have s2 := Sh_dup false (insert b E) v' a (k + 1) (Finset.mem_insert_of_mem haE)
            (by rw [Finset.mem_insert, not_or]; exact ⟨by omega, hk1E⟩)
            (fun p _ => by rw [v'1, v'l a hak]) j lf 10 _ (hD8 D h1) s1
          refine hcomb (insert (k + 1) (insert b E)) _ _ (k + 1) b (by simp) (by simp)
            (by omega) ?_ v'1 (v'l b hbk) s2
          ext w
          simp only [Finset.mem_erase, Finset.mem_insert]
          constructor
          · rintro ⟨n2, n1, h | h | h⟩
            · exact absurd h n1
            · exact absurd h n2
            · exact h
          · intro h
            have := hElt w h
            exact ⟨fun h' => hbE (h' ▸ h), by omega, Or.inr (Or.inr h)⟩
      · have hP : ∀ w ∈ insert a E, w < k := by
          intro w hw
          rcases Finset.mem_insert.mp hw with rfl | hw
          · exact hak
          · exact hElt w hw
        by_cases hbE : b ∈ E
        ·
          obtain ⟨D, h1, h2, j, h3, h4⟩ := IH (insert a E) hP (by
            intro w hw
            rcases Finset.mem_insert.mp hw with rfl | hw
            · exact hant.1
            · exact hEnt w hw)
          rw [Finset.card_insert_of_notMem haE] at h3
          refine ⟨D, h1, hdet (insert a E) D (fun w hw => Finset.mem_insert_of_mem hw)
            (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem hbE) h2, j + 1,
            by rw [hlen]; omega, ?_⟩
          have s1 := hstart (insert a E) _ j hP h4
          have s2 := Sh_dup false (insert a E) v' b (k + 2) (Finset.mem_insert_of_mem hbE)
            (by rw [Finset.mem_insert, not_or]; exact ⟨by omega, hk2E⟩)
            (fun p _ => by rw [v'2, v'l b hbk]) j lf 10 _ (hD8 D h1) s1
          refine hcomb (insert (k + 2) (insert a E)) _ _ a (k + 2) (by simp) (by simp)
            (by omega) ?_ (v'l a hak) v'2 s2
          ext w
          simp only [Finset.mem_erase, Finset.mem_insert]
          constructor
          · rintro ⟨n2, n1, h | h | h⟩
            · exact absurd h n2
            · exact absurd h n1
            · exact h
          · intro h
            have := hElt w h
            exact ⟨by omega, fun h' => haE (h' ▸ h), Or.inr (Or.inr h)⟩
        ·
          have hbaE : b ∉ insert a E := by
            rw [Finset.mem_insert, not_or]; exact ⟨fun h => hab h.symm, hbE⟩
          have hP2 : ∀ w ∈ insert b (insert a E), w < k := by
            intro w hw
            rcases Finset.mem_insert.mp hw with rfl | hw
            · exact hbk
            · exact hP w hw
          obtain ⟨D, h1, h2, j, h3, h4⟩ := IH (insert b (insert a E)) hP2 (by
            intro w hw
            rcases Finset.mem_insert.mp hw with rfl | hw
            · exact hant.2
            · rcases Finset.mem_insert.mp hw with rfl | hw
              · exact hant.1
              · exact hEnt w hw)
          rw [Finset.card_insert_of_notMem hbaE, Finset.card_insert_of_notMem haE] at h3
          refine ⟨D, h1, hdet _ D (fun w hw => Finset.mem_insert_of_mem
            (Finset.mem_insert_of_mem hw)) (by simp) (by simp) h2, j, by rw [hlen]; omega, ?_⟩
          have s1 := hstart _ _ j hP2 h4
          refine hcomb (insert b (insert a E)) _ _ a b (by simp) (by simp) hab ?_ (v'l a hak)
            (v'l b hbk) s1
          ext w
          simp only [Finset.mem_erase, Finset.mem_insert]
          constructor
          · rintro ⟨n2, n1, h | h | h⟩
            · exact absurd h n2
            · exact absurd h n1
            · exact h
          · intro h
            exact ⟨fun h' => hbE (h' ▸ h), fun h' => haE (h' ▸ h), Or.inr (Or.inr h)⟩

theorem mono (gs : List Gate) : (∀ g ∈ gs, Good g) → ∀ x y : List Bool, x.length = y.length →
    (∀ i, x.getD i false = true → y.getD i false = true) →
    ∀ i, (W gs x).getD i false = true → (W gs y).getD i false = true := by
  induction gs using List.reverseRecOn with
  | nil => intro _ x y _ h i hi; exact h i hi
  | append_singleton gs g ih =>
    intro hg x y hxy h i hi
    have IH := ih (fun g' h => hg g' (by simp [h])) x y hxy h
    have hgg : Good g := hg g (by simp)
    have hL : (W gs x).length = (W gs y).length := by rw [W_len, W_len, hxy]
    rw [W_snoc, stp] at hi ⊢
    rcases lt_trichotomy i (W gs x).length with h1 | h1 | h1
    · rw [getD_lt _ _ _ h1] at hi
      rw [getD_lt _ _ _ (hL ▸ h1)]
      exact IH i hi
    · rw [h1, getD_len] at hi
      rw [h1, hL, getD_len]
      rcases hgg.1 with ho | ho
      · rw [ho] at hi ⊢
        simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id] at hi ⊢
        exact fun j hj => IH j (hi j hj)
      · rw [ho] at hi ⊢
        simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id] at hi ⊢
        obtain ⟨j, hj, hj'⟩ := hi
        exact ⟨j, hj, IH j hj'⟩
    · rw [getD_big _ _ (by simp; omega)] at hi
      exact absurd hi (by simp)

def ro (v : Fin 5) : List Bool := List.replicate 5 false ++ List.ofFn (fun j : Fin 5 => decide (j = v))
def lo (u : Fin 5) : List Bool := List.ofFn (fun j : Fin 5 => decide (j = u)) ++ List.replicate 5 false

theorem agree1 : ∀ (u : Fin 5) (v : Fin 5), ∀ i < 10, i ≠ (u : ℕ) →
    (oneEach u v).getD i false = (ro v).getD i false := by decide +kernel
theorem agree2 : ∀ (u : Fin 5) (v : Fin 5), ∀ i < 10, i ≠ 5 + (v : ℕ) →
    (oneEach u v).getD i false = (lo u).getD i false := by decide +kernel
theorem below1 : ∀ (u : Fin 5) (v : Fin 5), ∀ i < 10, (ro v).getD i false = true →
    (oneEach u v).getD i false = true := by decide +kernel
theorem below2 : ∀ (u : Fin 5) (v : Fin 5), ∀ i < 10, (lo u).getD i false = true →
    (oneEach u v).getD i false = true := by decide +kernel
theorem oe_len : ∀ (u : Fin 5) (v : Fin 5), (oneEach u v).length = 10 := by decide +kernel
theorem ro_len : ∀ v : Fin 5, (ro v).length = 10 := by decide +kernel
theorem lo_len : ∀ v : Fin 5, (lo v).length = 10 := by decide +kernel

theorem below_of (x y : List Bool) (hx : x.length = 10)
    (h : ∀ i < 10, x.getD i false = true → y.getD i false = true) :
    ∀ i, x.getD i false = true → y.getD i false = true := by
  intro i hi
  by_cases h8 : i < 10
  · exact h i h8 hi
  · rw [getD_big _ _ (by omega)] at hi; exact absurd hi (by simp)

theorem row_in (C : Circuit) (hC : ∀ g ∈ C.gates, Good g) (A : Fin 5 → Fin 5 → Bool)
    (hrep : Represents A C) (D : Finset ℕ) (hD8 : D ⊆ Finset.range 10)
    (hD : ∀ x y : List Bool, x.length = 10 → y.length = 10 →
      (∀ i ∈ D, x.getD i false = y.getD i false) → C.eval x = C.eval y) (u : Fin 5)
    (hu : (u : ℕ) ∉ D) : ∀ u' v, A u v = true → A u' v = true := by
  intro u' v h
  rw [← hrep u v, hD (oneEach u v) (ro v) (oe_len u v) (ro_len v) (fun i hi =>
    agree1 u v i (by simpa using hD8 hi) (fun h => hu (h ▸ hi)))] at h
  rw [← hrep u' v]
  exact mono C.gates hC (ro v) (oneEach u' v) (by rw [ro_len, oe_len])
    (below_of _ _ (ro_len v) (below1 u' v)) C.output h

theorem col_in (C : Circuit) (hC : ∀ g ∈ C.gates, Good g) (A : Fin 5 → Fin 5 → Bool)
    (hrep : Represents A C) (D : Finset ℕ) (hD8 : D ⊆ Finset.range 10)
    (hD : ∀ x y : List Bool, x.length = 10 → y.length = 10 →
      (∀ i ∈ D, x.getD i false = y.getD i false) → C.eval x = C.eval y) (v : Fin 5)
    (hv : 5 + (v : ℕ) ∉ D) : ∀ v' u, A u v = true → A u v' = true := by
  intro v' u h
  rw [← hrep u v, hD (oneEach u v) (lo u) (oe_len u v) (lo_len u) (fun i hi =>
    agree2 u v i (by simpa using hD8 hi) (fun h => hv (h ▸ hi)))] at h
  rw [← hrep u v']
  exact mono C.gates hC (lo u) (oneEach u v') (by rw [lo_len, oe_len])
    (below_of _ _ (lo_len u) (below2 u v')) C.output h

def R8 : Finset ℕ := {1, 2, 3, 4, 5, 6, 7, 8}

theorem lower6 : ¬ RepSizeAtMost (fun (u : Fin 5) (v : Fin 5) => MM.testBit (5 * u.val + v.val)) 6 := by
  intro hrs
  obtain ⟨C, hgood, hsize, hrep, hirr⟩ := min_circ _ 6 hrs
  have hrow : ∀ u : Fin 5, (u : ℕ) ∈ R8 → ∃ (u' : Fin 5) (v : Fin 5),
      MM.testBit (5 * u + v) = true ∧ MM.testBit (5 * u' + v) = false := by decide +kernel
  have hcol : ∀ v : Fin 5, 5 + (v : ℕ) ∈ R8 → ∃ (v' : Fin 5) (u : Fin 5),
      MM.testBit (5 * u + v) = true ∧ MM.testBit (5 * u + v') = false := by decide +kernel
  have hR8 : ∀ i ∈ R8, i < 10 := by decide
  have hcard : R8.card = 8 := by decide
  have hnt : ∃ p < 25, MM.testBit p = false := ⟨0, by decide, by decide +kernel⟩
  have hRD : ∀ D : Finset ℕ, D ⊆ Finset.range 10 →
      (∀ x y : List Bool, x.length = 10 → y.length = 10 →
        (∀ i ∈ D, x.getD i false = y.getD i false) → C.eval x = C.eval y) → R8 ⊆ D := by
    intro D hD8 hD i hi
    by_contra hiD
    have hi8 := hR8 i hi
    by_cases h4 : i < 5
    · obtain ⟨u', v, h1, h2⟩ := hrow ⟨i, h4⟩ hi
      have := row_in C hgood _ hrep D hD8 hD ⟨i, h4⟩ hiD u' v h1
      rw [h2] at this; exact absurd this (by simp)
    · have e : 5 + (i - 5) = i := by omega
      obtain ⟨v', u, h1, h2⟩ := hcol ⟨i - 5, by omega⟩ (by simpa [e] using hi)
      have := col_in C hgood _ hrep D hD8 hD ⟨i - 5, by omega⟩ (by simpa [e] using hiD) v' u h1
      rw [h2] at this; exact absurd this (by simp)
  have hev : ∀ x, C.eval x = (W C.gates x).getD C.output false := fun x => rfl
  have hv : ∀ p < 25, vl C.gates C.output p = MM.testBit p := by
    intro p hp
    unfold vl
    rw [← hev]
    have h := hrep ⟨p / 5 % 5, by omega⟩ ⟨p % 5, by omega⟩
    have e : 5 * (p / 5 % 5) + p % 5 = p := by omega
    simp only [e] at h
    exact h
  by_cases ho : C.output < 10 + C.gates.length
  swap
  · have := Finset.card_le_card (hRD ∅ (by simp) (fun x y hx hy _ => by
      rw [hev, hev, getD_big _ _ (by rw [W_len]; omega), getD_big _ _ (by rw [W_len]; omega)]))
    rw [Finset.card_empty] at this; omega
  · obtain ⟨D, d1, d2, j, d3, d4⟩ := main C.gates hgood hirr {C.output} (by simpa using ho) (by
      intro w hw
      rw [Finset.mem_singleton] at hw
      obtain ⟨p, hp, h⟩ := hnt
      exact ⟨p, hp, by rw [hw, hv p hp]; exact h⟩)
    rw [Finset.card_singleton] at d3
    have hsub := hRD D d1 (fun x y hx hy hxy => d2 x y hx hy hxy C.output (by simp))
    have hle := Finset.card_le_card hsub
    omega

def witness : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.and, [10, 11]⟩, ⟨GateOp.or, [3, 4]⟩,
    ⟨GateOp.or, [7, 8]⟩, ⟨GateOp.and, [13, 14]⟩, ⟨GateOp.or, [12, 15]⟩], 16⟩

theorem witness_mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem witness_represents :
    Represents (fun u v : Fin 5 => (12979296 : ℕ).testBit (5 * u.val + v.val)) witness := by
  decide

end PEqualNP.Outside.L_meta_20613

theorem PEqualNP.Outside.L_meta_20613 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (12979296 : ℕ).testBit (5 * u.val + v.val)) 7 ∧ ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (12979296 : ℕ).testBit (5 * u.val + v.val)) 6 :=
  ⟨⟨PEqualNP.Outside.L_meta_20613.witness, PEqualNP.Outside.L_meta_20613.witness_mono, by decide,
    PEqualNP.Outside.L_meta_20613.witness_represents⟩, PEqualNP.Outside.L_meta_20613.lower6⟩
