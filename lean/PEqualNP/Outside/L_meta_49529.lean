import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_49529_aux
open PEqualNP.CircuitLowerBounds

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
def W (gs : List Gate) (x : List Bool) : List Bool := gs.foldl stepW x
lemma W_append (gs : List Gate) (g : Gate) (x : List Bool) :
    W (gs ++ [g]) x = stepW (W gs x) g := by
  simp [W, List.foldl_append]
lemma W_length (gs : List Gate) (x : List Bool) : (W gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [W]
  | append_singleton gs g ih => rw [W_append]; simp [stepW, ih]; omega
lemma W_getD_lt (gs : List Gate) (g : Gate) (x : List Bool) (k : ℕ)
    (hk : k < (W gs x).length) : (W (gs ++ [g]) x).getD k false = (W gs x).getD k false := by
  rw [W_append, stepW]
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hk]
lemma W_getD_last (gs : List Gate) (g : Gate) (x : List Bool) :
    (W (gs ++ [g]) x).getD (x.length + gs.length) false =
      g.op.eval (g.inputs.map fun i => (W gs x).getD i false) := by
  rw [W_append, stepW]
  have := W_length gs x
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
  simp [this]
lemma W_prefix (as bs : List Gate) (x : List Bool) (k : ℕ) (hk : k < x.length + as.length) :
    (W (as ++ bs) x).getD k false = (W as x).getD k false := by
  induction bs using List.reverseRecOn with
  | nil => simp
  | append_singleton bs g ih =>
    rw [← List.append_assoc, W_getD_lt _ _ _ _ (by rw [W_length]; simp; omega), ih]

def OKg (g : Gate) (b : ℕ) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2 ∧
    ∀ i ∈ g.inputs, i < b

def Good (N : ℕ) (gs : List Gate) : Prop := ∀ j (h : j < gs.length), OKg gs[j] (N + j)

lemma Good_snoc {N : ℕ} {gs : List Gate} {g : Gate} (h : Good N gs) (hg : OKg g (N + gs.length)) :
    Good N (gs ++ [g]) := by
  intro j hj
  simp only [List.length_append, List.length_singleton] at hj
  by_cases hj' : j < gs.length
  · rw [List.getElem_append_left hj']; exact h j hj'
  · have : j = gs.length := by omega
    subst this
    simpa using hg

def isNot : GateOp → Bool
  | GateOp.not => true
  | _ => false
def nc (gs : List Gate) : ℕ := (gs.filter fun g => isNot g.op).length
lemma nc_append (a b : List Gate) : nc (a ++ b) = nc a + nc b := by simp [nc, List.filter_append]
lemma nc_and (l : List ℕ) : nc [⟨GateOp.and, l⟩] = 0 := by simp [nc, isNot]
lemma nc_or (l : List ℕ) : nc [⟨GateOp.or, l⟩] = 0 := by simp [nc, isNot]
lemma nc_nil : nc [] = 0 := rfl

section Rep
variable {X : Type} (N : ℕ) (env : X → List Bool)

def Rep (gs : List Gate) (w : ℕ) (P : X → Prop) : Prop :=
  w < N + gs.length ∧ ∀ x, ((W gs (env x)).getD w false = true ↔ P x)

variable {N env}

lemma Rep_ext (hN : ∀ x, (env x).length = N) {gs : List Gate} {w : ℕ} {P : X → Prop}
    (h : Rep N env gs w P) (hs : List Gate) : Rep N env (gs ++ hs) w P := by
  refine ⟨by simp; have := h.1; omega, fun x => ?_⟩
  rw [W_prefix _ _ _ _ (by rw [hN]; exact h.1)]
  exact h.2 x

lemma Rep_congr {gs : List Gate} {w : ℕ} {P Q : X → Prop} (h : Rep N env gs w P)
    (hPQ : ∀ x, P x ↔ Q x) : Rep N env gs w Q :=
  ⟨h.1, fun x => (h.2 x).trans (hPQ x)⟩

lemma Rep_gate (hN : ∀ x, (env x).length = N) (gs : List Gate) (g : Gate) (x : X) :
    (W (gs ++ [g]) (env x)).getD (N + gs.length) false =
      g.op.eval (g.inputs.map fun i => (W gs (env x)).getD i false) := by
  have := W_getD_last gs g (env x)
  rwa [hN] at this

def Ext (gs : List Gate) (c : ℕ) (Φ : List Gate → ℕ → Prop) : Prop :=
  ∃ hs w, Good N (gs ++ hs) ∧ nc hs = 0 ∧ hs.length ≤ c ∧ Φ (gs ++ hs) w

lemma ext_and2 (hN : ∀ x, (env x).length = N) {gs : List Gate} (hG : Good N gs) {a b : ℕ}
    {P Q : X → Prop} (ha : Rep N env gs a P) (hb : Rep N env gs b Q) :
    Ext (N := N) gs 1 (fun gs' w => Rep N env gs' w (fun x => P x ∧ Q x)) := by
  refine ⟨[⟨GateOp.and, [a, b]⟩], N + gs.length, Good_snoc hG ⟨by simp, by simp, ?_⟩,
    nc_and _, by simp, by simp, fun x => ?_⟩
  · intro i hi; simp at hi; rcases hi with rfl | rfl; exact ha.1; exact hb.1
  · have h1 := ha.2 x; have h2 := hb.2 x
    simp only [List.getD_eq_getElem?_getD] at h1 h2
    rw [Rep_gate hN]; simp [GateOp.eval, h1, h2]

lemma ext_or2 (hN : ∀ x, (env x).length = N) {gs : List Gate} (hG : Good N gs) {a b : ℕ}
    {P Q : X → Prop} (ha : Rep N env gs a P) (hb : Rep N env gs b Q) :
    Ext (N := N) gs 1 (fun gs' w => Rep N env gs' w (fun x => P x ∨ Q x)) := by
  refine ⟨[⟨GateOp.or, [a, b]⟩], N + gs.length, Good_snoc hG ⟨by simp, by simp, ?_⟩,
    nc_or _, by simp, by simp, fun x => ?_⟩
  · intro i hi; simp at hi; rcases hi with rfl | rfl; exact ha.1; exact hb.1
  · have h1 := ha.2 x; have h2 := hb.2 x
    simp only [List.getD_eq_getElem?_getD] at h1 h2
    rw [Rep_gate hN]; simp [GateOp.eval, h1, h2]

lemma ext_false (hN : ∀ x, (env x).length = N) {gs : List Gate} (hG : Good N gs) :
    Ext (N := N) gs 1 (fun gs' w => Rep N env gs' w (fun _ => False)) := by
  refine ⟨[⟨GateOp.or, []⟩], N + gs.length, Good_snoc hG ⟨by simp, by simp, by simp⟩,
    nc_or _, by simp, by simp, fun x => ?_⟩
  rw [Rep_gate hN]; simp [GateOp.eval]

lemma ext_true (hN : ∀ x, (env x).length = N) {gs : List Gate} (hG : Good N gs) :
    Ext (N := N) gs 1 (fun gs' w => Rep N env gs' w (fun _ => True)) := by
  refine ⟨[⟨GateOp.and, []⟩], N + gs.length, Good_snoc hG ⟨by simp, by simp, by simp⟩,
    nc_and _, by simp, by simp, fun x => ?_⟩
  rw [Rep_gate hN]; simp [GateOp.eval]

lemma rep_not (hN : ∀ x, (env x).length = N) {gs : List Gate} (hG : Good N gs) {a : ℕ}
    {P : X → Prop} (ha : Rep N env gs a P) :
    Good N (gs ++ [⟨GateOp.not, [a]⟩]) ∧ nc [⟨GateOp.not, [a]⟩] = 1 ∧
      Rep N env (gs ++ [⟨GateOp.not, [a]⟩]) (N + gs.length) (fun x => ¬ P x) := by
  refine ⟨Good_snoc hG ⟨by simp, by simp, ?_⟩, by simp [nc, isNot], by simp, fun x => ?_⟩
  · intro i hi; simp at hi; subst hi; exact ha.1
  · have h1 := ha.2 x
    simp only [List.getD_eq_getElem?_getD] at h1
    rw [Rep_gate hN]; simp [GateOp.eval]; rw [← h1]; simp

lemma Ext.bind {gs : List Gate} {c d : ℕ} {Φ Ψ : List Gate → ℕ → Prop}
    (h : Ext (N := N) gs c Φ)
    (k : ∀ hs w, Good N (gs ++ hs) → Φ (gs ++ hs) w →
      ∃ hs' w', Good N (gs ++ hs ++ hs') ∧ nc hs' = 0 ∧ hs'.length ≤ d ∧ Ψ (gs ++ hs ++ hs') w') :
    Ext (N := N) gs (c + d) Ψ := by
  obtain ⟨hs, w, hG, hn, hl, hΦ⟩ := h
  obtain ⟨hs', w', hG', hn', hl', hΨ⟩ := k hs w hG hΦ
  refine ⟨hs ++ hs', w', by simpa using hG', by rw [nc_append]; omega, by simp; omega, by simpa using hΨ⟩

lemma family (hN : ∀ x, (env x).length = N) (L : List ℕ) (c : ℕ → ℕ)
    (Q : ℕ → X → Prop) (Pre : List Gate → Prop)
    (hPre : ∀ gs hs, Pre gs → Pre (gs ++ hs))
    (step : ∀ i ∈ L, ∀ gs, Good N gs → Pre gs →
      Ext (N := N) gs (c i) (fun gs' w => Rep N env gs' w (Q i))) :
    ∀ gs, Good N gs → Pre gs → ∃ hs, ∃ f : ℕ → ℕ, Good N (gs ++ hs) ∧ nc hs = 0 ∧
      hs.length ≤ (L.map c).sum ∧ ∀ i ∈ L, Rep N env (gs ++ hs) (f i) (Q i) := by
  induction L with
  | nil => intro gs hG _; exact ⟨[], fun _ => 0, by simpa using hG, rfl, by simp, by simp⟩
  | cons i0 L ih =>
    intro gs hG hP
    obtain ⟨hs, f, hG1, hn1, hl1, hR⟩ := ih (fun i hi => step i (by simp [hi])) gs hG hP
    obtain ⟨hs', w, hG2, hn2, hl2, hR'⟩ := step i0 (by simp) (gs ++ hs) hG1 (hPre _ _ hP)
    refine ⟨hs ++ hs', Function.update f i0 w, by simpa using hG2, by rw [nc_append]; omega,
      by simp; omega, ?_⟩
    intro i hi
    by_cases e : i = i0
    · subst e; simpa using hR'
    · rw [Function.update_of_ne e]
      have hi' : i ∈ L := by simpa [e] using hi
      simpa using Rep_ext hN (hR i hi') hs'

lemma bigOr (hN : ∀ x, (env x).length = N) {gs : List Gate} (hG : Good N gs) (L : List ℕ)
    (f : ℕ → ℕ) (P : ℕ → X → Prop) (h : ∀ i ∈ L, Rep N env gs (f i) (P i)) :
    Ext (N := N) gs (L.length + 1) (fun gs' w => Rep N env gs' w (fun x => ∃ i ∈ L, P i x)) := by
  induction L with
  | nil => exact (ext_false hN hG).imp fun hs ⟨w, a, b, c, d⟩ => ⟨w, a, b, c, Rep_congr d (by simp)⟩
  | cons i0 L ih =>
    obtain ⟨hs, w, hG1, hn1, hl1, hR⟩ := ih (fun i hi => h i (by simp [hi]))
    obtain ⟨hs', w', hG2, hn2, hl2, hR'⟩ := ext_or2 hN hG1 hR (Rep_ext hN (h i0 (by simp)) hs)
    refine ⟨hs ++ hs', w', by simpa using hG2, by rw [nc_append]; omega, by simp; omega, ?_⟩
    simp only [← List.append_assoc]
    exact Rep_congr hR' (fun x => by simp; exact or_comm)

lemma bigAnd (hN : ∀ x, (env x).length = N) {gs : List Gate} (hG : Good N gs) (L : List ℕ)
    (f : ℕ → ℕ) (P : ℕ → X → Prop) (h : ∀ i ∈ L, Rep N env gs (f i) (P i)) :
    Ext (N := N) gs (L.length + 1) (fun gs' w => Rep N env gs' w (fun x => ∀ i ∈ L, P i x)) := by
  induction L with
  | nil => exact (ext_true hN hG).imp fun hs ⟨w, a, b, c, d⟩ => ⟨w, a, b, c, Rep_congr d (by simp)⟩
  | cons i0 L ih =>
    obtain ⟨hs, w, hG1, hn1, hl1, hR⟩ := ih (fun i hi => h i (by simp [hi]))
    obtain ⟨hs', w', hG2, hn2, hl2, hR'⟩ := ext_and2 hN hG1 hR (Rep_ext hN (h i0 (by simp)) hs)
    refine ⟨hs ++ hs', w', by simpa using hG2, by rw [nc_append]; omega, by simp; omega, ?_⟩
    simp only [← List.append_assoc]
    exact Rep_congr hR' (fun x => by simp; exact and_comm)

lemma scan (hN : ∀ x, (env x).length = N) {gs : List Gate} (hG : Good N gs) (K : ℕ)
    (f : ℕ → ℕ) (P : ℕ → X → Prop) (h : ∀ i < K, Rep N env gs (f i) (P i)) :
    ∃ hs, ∃ p : ℕ → ℕ, Good N (gs ++ hs) ∧ nc hs = 0 ∧ hs.length ≤ K + 1 ∧
      ∀ k ≤ K, Rep N env (gs ++ hs) (p k) (fun x => ∀ i < k, P i x) := by
  induction K with
  | zero =>
    obtain ⟨hs, w, a, b, c, d⟩ := ext_true hN hG
    exact ⟨hs, fun _ => w, a, b, c, fun k hk => Rep_congr d (by intro x; simp; omega)⟩
  | succ K ih =>
    obtain ⟨hs, p, hG1, hn1, hl1, hR⟩ := ih (fun i hi => h i (by omega))
    obtain ⟨hs', w', hG2, hn2, hl2, hR'⟩ :=
      ext_and2 hN hG1 (hR K le_rfl) (Rep_ext hN (h K (by omega)) hs)
    refine ⟨hs ++ hs', Function.update p (K+1) w', by simpa using hG2, by rw [nc_append]; omega,
      by simp; omega, ?_⟩
    intro k hk
    by_cases e : k = K + 1
    · subst e; simp only [Function.update_self, ← List.append_assoc]
      exact Rep_congr hR' (fun x => ⟨fun ⟨h1, h2⟩ i hi => by
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
        · exact h1 i hi
        · exact h2, fun H => ⟨fun i hi => H i (by omega), H K (by omega)⟩⟩)
    · rw [Function.update_of_ne e, ← List.append_assoc]
      exact Rep_ext hN (hR k (by omega)) hs'

end Rep

section Dom
variable (n : ℕ)

noncomputable def env (x : Finset (Fin n)) : List Bool :=
  List.ofFn (fun u : Fin n => @decide (u ∈ x) (Classical.propDecidable _)) ++ [false, true]

lemma env_len : ∀ x, (env n x).length = n + 2 := by intro x; simp [env]

def IvOr (a L : ℕ) (x : Finset (Fin n)) : Prop := ∃ v ∈ x, a ≤ v.val ∧ v.val < a + L

lemma rep_input (u : ℕ) (hu : u < n) :
    Rep (n+2) (env n) [] u (fun x => ∃ v ∈ x, v.val = u) := by
  refine ⟨by simp; omega, fun x => ?_⟩
  simp only [W, List.foldl_nil, env, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by simp; exact hu)]
  simp only [List.getElem?_ofFn]
  simp only [hu, ↓reduceDIte, Option.getD_some, decide_eq_true_iff]
  constructor
  · intro h; exact ⟨_, h, rfl⟩
  · rintro ⟨v, hv, rfl⟩; exact hv

lemma rep_input' {gs : List Gate} (u : ℕ) (hu : u < n) :
    Rep (n+2) (env n) gs u (fun x => ∃ v ∈ x, v.val = u) := by
  simpa using Rep_ext (env_len n) (rep_input n u hu) gs

def TabOK (gs : List Gate) (K : ℕ) (tab : ℕ → ℕ → ℕ) : Prop :=
  ∀ ℓ ≤ K, ∀ a, a + 2 ^ ℓ ≤ n → Rep (n+2) (env n) gs (tab ℓ a) (IvOr n a (2 ^ ℓ))

lemma TabOK_ext {gs : List Gate} {K : ℕ} {tab : ℕ → ℕ → ℕ} (h : TabOK n gs K tab) (hs : List Gate) :
    TabOK n (gs ++ hs) K tab := fun ℓ hℓ a ha => Rep_ext (env_len n) (h ℓ hℓ a ha) hs

lemma table (K : ℕ) : ∀ gs, Good (n+2) gs → ∃ hs, ∃ tab : ℕ → ℕ → ℕ, Good (n+2) (gs ++ hs) ∧
    nc hs = 0 ∧ hs.length ≤ K * n ∧ TabOK n (gs ++ hs) K tab := by
  induction K with
  | zero =>
    intro gs hG
    refine ⟨[], fun _ a => a, by simpa using hG, rfl, by simp, ?_⟩
    intro ℓ hℓ a ha
    have hℓ0 : ℓ = 0 := by omega
    subst hℓ0
    refine Rep_congr (rep_input' n a (by simp at ha; omega)) (fun x => ?_)
    simp only [IvOr, pow_zero]
    constructor
    · rintro ⟨v, hv, rfl⟩; exact ⟨v, hv, le_rfl, by omega⟩
    · rintro ⟨v, hv, h1, h2⟩; exact ⟨v, hv, by omega⟩
  | succ K ih =>
    intro gs hG
    obtain ⟨hs, tab, hG1, hn1, hl1, hT⟩ := ih gs hG
    obtain ⟨hs', f, hG2, hn2, hl2, hR⟩ := family (env_len n) (List.range n) (fun _ => 1)
      (fun a x => a + 2 ^ (K+1) ≤ n → IvOr n a (2 ^ (K+1)) x) (fun gs => TabOK n gs K tab)
      (fun gs hs h => TabOK_ext n h hs) (by
        intro a _ gs hG h
        by_cases ha : a + 2 ^ (K+1) ≤ n
        · have hp : 2 ^ (K+1) = 2 ^ K + 2 ^ K := by rw [pow_succ]; ring
          have hpos : 0 < 2 ^ K := by positivity
          have ha' : a + (2 ^ K + 2 ^ K) ≤ n := by omega
          obtain ⟨hs, w, a1, a2, a3, a4⟩ := ext_or2 (env_len n) hG (h K le_rfl a (by omega))
            (h K le_rfl (a + 2 ^ K) (by omega))
          refine ⟨hs, w, a1, a2, a3, Rep_congr a4 (fun x => ?_)⟩
          simp only [IvOr, hp, ha', true_implies]
          constructor
          · rintro (⟨v, hv, h1, h2⟩ | ⟨v, hv, h1, h2⟩) <;> exact ⟨v, hv, by omega, by omega⟩
          · rintro ⟨v, hv, h1, h2⟩
            by_cases hv' : v.val < a + 2 ^ K
            · exact Or.inl ⟨v, hv, h1, hv'⟩
            · exact Or.inr ⟨v, hv, by omega, by omega⟩
        · obtain ⟨hs, w, a1, a2, a3, a4⟩ := ext_true (env_len n) hG
          exact ⟨hs, w, a1, a2, a3, Rep_congr a4 (fun x => by simp [ha])⟩) (gs ++ hs) hG1 hT
    refine ⟨hs ++ hs', fun ℓ a => if ℓ = K + 1 then f a else tab ℓ a, by simpa using hG2,
      by rw [nc_append]; omega, ?_, ?_⟩
    · simp at hl2 ⊢; rw [Nat.succ_mul]; omega
    · intro ℓ hℓ a ha
      rw [← List.append_assoc]
      by_cases e : ℓ = K + 1
      · subst e
        simp only [ite_true]
        have hpos : 0 < 2 ^ (K+1) := by positivity
        exact Rep_congr (hR a (by simp; omega)) (fun x => by simp [ha])
      · simp only [e, ite_false]
        exact Rep_ext (env_len n) (hT ℓ (by omega) a ha) hs'

lemma interval {gs : List Gate} (hG : Good (n+2) gs) {K : ℕ} {tab : ℕ → ℕ → ℕ}
    (hT : TabOK n gs K tab) (hK : Nat.log2 n ≤ K) (a L : ℕ) (h : a + L ≤ n) :
    Ext (N := n+2) gs 1 (fun gs' w => Rep (n+2) (env n) gs' w (IvOr n a L)) := by
  by_cases hL : L = 0
  · subst hL
    obtain ⟨hs, w, a1, a2, a3, a4⟩ := ext_false (env_len n) hG
    exact ⟨hs, w, a1, a2, a3, Rep_congr a4 (fun x => by simp [IvOr])⟩
  · have h1 : 2 ^ L.log2 ≤ L := Nat.log2_self_le hL
    have h2 : L < 2 ^ (L.log2 + 1) := Nat.lt_log2_self
    have h3 : L.log2 ≤ K := le_trans (by
      rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]; exact Nat.log_mono_right (by omega)) hK
    have hp : 2 ^ (L.log2 + 1) = 2 ^ L.log2 + 2 ^ L.log2 := by rw [pow_succ]; ring
    obtain ⟨hs, w, a1, a2, a3, a4⟩ := ext_or2 (env_len n) hG (hT _ h3 a (by omega))
      (hT _ h3 (a + L - 2 ^ L.log2) (by omega))
    refine ⟨hs, w, a1, a2, a3, Rep_congr a4 (fun x => ?_)⟩
    simp only [IvOr]
    constructor
    · rintro (⟨v, hv, h1, h2⟩ | ⟨v, hv, h1, h2⟩) <;> exact ⟨v, hv, by omega, by omega⟩
    · rintro ⟨v, hv, h4, h5⟩
      by_cases hv' : v.val < a + 2 ^ L.log2
      · exact Or.inl ⟨v, hv, h4, hv'⟩
      · exact Or.inr ⟨v, hv, by omega, by omega⟩

end Dom

section Gap
open Classical

noncomputable def gapEnd (mk : ℕ → Prop) (n a : ℕ) : ℕ :=
  @Nat.find (fun v => a ≤ v ∧ (n ≤ v ∨ mk v)) (Classical.decPred _)
    ⟨max a n, le_max_left _ _, Or.inl (le_max_right _ _)⟩

lemma gapEnd_spec (mk : ℕ → Prop) (n a : ℕ) :
    a ≤ gapEnd mk n a ∧ (n ≤ gapEnd mk n a ∨ mk (gapEnd mk n a)) := by
  unfold gapEnd
  exact @Nat.find_spec (fun v => a ≤ v ∧ (n ≤ v ∨ mk v)) (Classical.decPred _)
    ⟨max a n, le_max_left _ _, Or.inl (le_max_right _ _)⟩

lemma gapEnd_min (mk : ℕ → Prop) (n a v : ℕ) (h1 : a ≤ v) (h2 : v < gapEnd mk n a) :
    v < n ∧ ¬ mk v := by
  unfold gapEnd at h2
  have := @Nat.find_min _ (Classical.decPred _) _ _ h2
  push Not at this
  have := this h1
  exact ⟨by omega, this.2⟩

lemma gapEnd_le (mk : ℕ → Prop) (n a : ℕ) (h : a ≤ n) : gapEnd mk n a ≤ n := by
  unfold gapEnd; exact @Nat.find_min' _ (Classical.decPred _) _ _ ⟨h, Or.inl le_rfl⟩

lemma gap_cover (mk : ℕ → Prop) (n v : ℕ) (hv : v < n) (hm : ¬ mk v) :
    ∃ a, (a = 0 ∨ (1 ≤ a ∧ mk (a - 1))) ∧ a ≤ v ∧ v < gapEnd mk n a := by
  have hex : ∃ a, a ≤ v ∧ ∀ w, a ≤ w → w ≤ v → ¬ mk w :=
    ⟨v, le_rfl, fun w h1 h2 => by have : w = v := by omega
                                  subst this; exact hm⟩
  set a := Nat.find hex with ha
  have hs := Nat.find_spec hex
  rw [← ha] at hs
  refine ⟨a, ?_, hs.1, ?_⟩
  · by_cases h0 : a = 0
    · exact Or.inl h0
    · right
      refine ⟨by omega, ?_⟩
      have hmin := Nat.find_min hex (show a - 1 < Nat.find hex by omega)
      push Not at hmin
      obtain ⟨w, hw1, hw2, hw3⟩ := hmin (by omega)
      by_cases hw : a ≤ w
      · exact absurd hw3 (hs.2 w hw hw2)
      · have : w = a - 1 := by omega
        rw [← this]; exact hw3
  · by_contra hc
    push Not at hc
    obtain ⟨he1, he2⟩ := gapEnd_spec mk n a
    rcases he2 with he2 | he2
    · omega
    · exact hs.2 _ he1 hc he2

variable {n m : ℕ} (g : Fin n → Fin m → Prop)

def mkj (j : Fin m) (v : ℕ) : Prop := ∃ h : v < n, g ⟨v, h⟩ j

noncomputable def rowsF (j : Fin m) : Finset ℕ :=
  (Finset.univ.filter (fun u : Fin n => g u j)).map Fin.valEmbedding

noncomputable def starts (j : Fin m) : Finset ℕ := insert 0 ((rowsF g j).image (· + 1))

lemma starts_card (j : Fin m) :
    (starts g j).card ≤ (Finset.univ.filter (fun u : Fin n => g u j)).card + 1 := by
  unfold starts
  refine le_trans (Finset.card_insert_le _ _) ?_
  have := Finset.card_image_le (s := rowsF g j) (f := (· + 1))
  have h2 : (rowsF g j).card = (Finset.univ.filter (fun u : Fin n => g u j)).card := by
    simp [rowsF]
  omega

lemma starts_le (j : Fin m) (a : ℕ) (ha : a ∈ starts g j) : a ≤ n := by
  simp only [starts, rowsF, Finset.mem_insert, Finset.mem_image, Finset.mem_map,
    Finset.mem_filter, Fin.valEmbedding_apply] at ha
  rcases ha with rfl | ⟨_, ⟨u, _, rfl⟩, rfl⟩
  · omega
  · have := u.2; omega

lemma dead_iff (j : Fin m) (x : Finset (Fin n)) :
    (∃ a ∈ (starts g j).toList, IvOr n a (gapEnd (mkj g j) n a - a) x) ↔ ∃ u ∈ x, ¬ g u j := by
  simp only [Finset.mem_toList, IvOr]
  constructor
  · rintro ⟨a, ha, v, hv, h1, h2⟩
    have hle := (gapEnd_spec (mkj g j) n a).1
    have := gapEnd_min (mkj g j) n a v h1 (by omega)
    exact ⟨v, hv, fun hg => this.2 ⟨v.2, hg⟩⟩
  · rintro ⟨u, hu, hg⟩
    obtain ⟨a, ha, h1, h2⟩ := gap_cover (mkj g j) n u.val u.2 (fun ⟨_, h⟩ => hg h)
    refine ⟨a, ?_, u, hu, h1, by omega⟩
    simp only [starts, rowsF, Finset.mem_insert, Finset.mem_image, Finset.mem_map,
      Finset.mem_filter, Fin.valEmbedding_apply, Finset.mem_univ, true_and]
    rcases ha with h | ⟨h3, h4, h5⟩
    · exact Or.inl h
    · right; exact ⟨a - 1, ⟨⟨a - 1, h4⟩, h5, rfl⟩, by omega⟩

lemma marked_iff (j : Fin m) (x : Finset (Fin n)) :
    (∃ u ∈ (rowsF g j).toList, ∃ v ∈ x, v.val = u) ↔ ∃ v ∈ x, g v j := by
  simp only [Finset.mem_toList, rowsF, Finset.mem_map, Finset.mem_filter, Finset.mem_univ,
    true_and, Fin.valEmbedding_apply]
  constructor
  · rintro ⟨_, ⟨u, hu, rfl⟩, v, hv, e⟩
    have : v = u := Fin.ext e
    subst this; exact ⟨v, hv, hu⟩
  · rintro ⟨v, hv, hg⟩; exact ⟨v, ⟨v, hg, rfl⟩, v, hv, rfl⟩

lemma dead_step {gs : List Gate} (hG : Good (n+2) gs) {K : ℕ} {tab : ℕ → ℕ → ℕ}
    (hT : TabOK n gs K tab) (hK : Nat.log2 n ≤ K) (j : Fin m) :
    Ext (N := n+2) gs (2 * (Finset.univ.filter (fun u : Fin n => g u j)).card + 3)
      (fun gs' w => Rep (n+2) (env n) gs' w (fun x => ∃ u ∈ x, ¬ g u j)) := by
  obtain ⟨hs, f, hG1, hn1, hl1, hR⟩ := family (env_len n) (starts g j).toList (fun _ => 1)
    (fun a => IvOr n a (gapEnd (mkj g j) n a - a)) (fun gs => TabOK n gs K tab)
    (fun gs hs h => TabOK_ext n h hs) (by
      intro a ha gs hG h
      have h1 := starts_le g j a (Finset.mem_toList.mp ha)
      have h2 := gapEnd_le (mkj g j) n a h1
      have h3 := (gapEnd_spec (mkj g j) n a).1
      exact interval n hG h hK a _ (by omega)) gs hG hT
  obtain ⟨hs', w, hG2, hn2, hl2, hR'⟩ := bigOr (env_len n) hG1 (starts g j).toList f _ hR
  have hc := starts_card g j
  refine ⟨hs ++ hs', w, by simpa using hG2, by rw [nc_append]; omega, ?_, ?_⟩
  · simp only [List.map_const', List.sum_replicate, smul_eq_mul, mul_one,
      Finset.length_toList] at hl1 hl2
    simp; omega
  · rw [← List.append_assoc]; exact Rep_congr hR' (dead_iff g j)

lemma marked_step {gs : List Gate} (hG : Good (n+2) gs) (j : Fin m) :
    Ext (N := n+2) gs ((Finset.univ.filter (fun u : Fin n => g u j)).card + 1)
      (fun gs' w => Rep (n+2) (env n) gs' w (fun x => ∃ u ∈ x, g u j)) := by
  have := bigOr (env_len n) hG (rowsF g j).toList id (fun u x => ∃ v ∈ x, v.val = u) (by
    intro u hu
    simp only [Finset.mem_toList, rowsF, Finset.mem_map, Fin.valEmbedding_apply] at hu
    obtain ⟨v, _, rfl⟩ := hu
    exact rep_input' n v.val v.2)
  obtain ⟨hs, w, a1, a2, a3, a4⟩ := this
  refine ⟨hs, w, a1, a2, by simpa [rowsF] using a3, Rep_congr a4 (marked_iff g j)⟩

end Gap

section Thr
variable {n : ℕ}

lemma t1_step {gs : List Gate} (hG : Good (n+2) gs) {K : ℕ} {tab : ℕ → ℕ → ℕ}
    (hT : TabOK n gs K tab) (hK : Nat.log2 n ≤ K) :
    Ext (N := n+2) gs 1 (fun gs' w => Rep (n+2) (env n) gs' w (fun x => ∃ v, v ∈ x)) := by
  obtain ⟨hs, w, a1, a2, a3, a4⟩ := interval n hG hT hK 0 n (by omega)
  refine ⟨hs, w, a1, a2, a3, Rep_congr a4 (fun x => ?_)⟩
  simp only [IvOr]
  exact ⟨fun ⟨v, hv, _⟩ => ⟨v, hv⟩, fun ⟨v, hv⟩ => ⟨v, hv, by omega, by have := v.2; omega⟩⟩

lemma t2_step {gs : List Gate} (hG : Good (n+2) gs) {K : ℕ} {tab : ℕ → ℕ → ℕ}
    (hT : TabOK n gs K tab) (hK : Nat.log2 n ≤ K) :
    Ext (N := n+2) gs (3 * n + 1)
      (fun gs' w => Rep (n+2) (env n) gs' w (fun x => ∃ v ∈ x, ∃ w ∈ x, v ≠ w)) := by
  obtain ⟨hs, f, hG1, hn1, hl1, hR⟩ := family (env_len n) (List.range n) (fun _ => 2)
    (fun u x => (∃ v ∈ x, v.val = u) ∧ IvOr n 0 u x) (fun gs => TabOK n gs K tab)
    (fun gs hs h => TabOK_ext n h hs) (by
      intro u hu gs hG h
      have hu' : u < n := List.mem_range.mp hu
      obtain ⟨hs, w, a1, a2, a3, a4⟩ := interval n hG h hK 0 u (by omega)
      obtain ⟨hs', w', b1, b2, b3, b4⟩ := ext_and2 (env_len n) a1
        (rep_input' n (gs := gs ++ hs) u hu') a4
      refine ⟨hs ++ hs', w', by simpa using b1, by rw [nc_append]; omega, by simp; omega,
        by simpa using b4⟩) gs hG hT
  obtain ⟨hs', w, hG2, hn2, hl2, hR'⟩ := bigOr (env_len n) hG1 (List.range n) f _ hR
  refine ⟨hs ++ hs', w, by simpa using hG2, by rw [nc_append]; omega, ?_, ?_⟩
  · simp only [List.map_const', List.sum_replicate, smul_eq_mul, List.length_range] at hl1 hl2
    simp; omega
  · rw [← List.append_assoc]
    refine Rep_congr hR' (fun x => ?_)
    simp only [List.mem_range, IvOr]
    constructor
    · rintro ⟨u, _, ⟨v, hv, rfl⟩, w, hw, _, h2⟩
      exact ⟨w, hw, v, hv, fun e => by rw [e] at h2; omega⟩
    · rintro ⟨v, hv, w, hw, hne⟩
      have hne' : v.val ≠ w.val := fun e => hne (Fin.ext e)
      rcases Nat.lt_or_gt_of_ne hne' with h | h
      · exact ⟨w.val, w.2, ⟨w, hw, rfl⟩, v, hv, by omega, by omega⟩
      · exact ⟨v.val, v.2, ⟨v, hv, rfl⟩, w, hw, by omega, by omega⟩

end Thr

section Main
open Classical
lemma logic {n m : ℕ} (g : Fin n → Fin m → Prop)
    (hsp : ∀ u v : Fin n, u ≠ v → ∀ j j' : Fin m, g u j → g v j → g u j' → g v j' → j = j')
    (x : Finset (Fin n)) (j : Fin m) (T1 T2 AD B0 : Prop)
    (hT1 : T1 ↔ ∃ v, v ∈ x) (hT2 : T2 ↔ ∃ v ∈ x, ∃ w ∈ x, v ≠ w)
    (hAD : AD ↔ ∀ i : Fin m, ∃ u ∈ x, ¬ g u i) (hB0 : B0 ↔ (T1 ∧ ¬ T2) ∨ (T2 ∧ AD)) :
    ((¬T2 ∧ ¬B0) ∨ ((¬T2 ∧ ∃ u ∈ x, g u j) ∨
      ((T2 ∧ (¬T2 ∨ ¬B0)) ∧ (∀ i : Fin m, i ≠ j → ∃ u ∈ x, ¬ g u i)))) ↔ ∀ u ∈ x, g u j := by
  by_cases h2 : T2
  · have hB : B0 ↔ AD := by tauto
    have e : ((¬T2 ∧ ¬B0) ∨ ((¬T2 ∧ ∃ u ∈ x, g u j) ∨
      ((T2 ∧ (¬T2 ∨ ¬B0)) ∧ (∀ i : Fin m, i ≠ j → ∃ u ∈ x, ¬ g u i)))) ↔
        (¬ AD ∧ ∀ i : Fin m, i ≠ j → ∃ u ∈ x, ¬ g u i) := by tauto
    rw [e, hAD]
    obtain ⟨v, hv, w, hw, hvw⟩ := hT2.mp h2
    constructor
    · rintro ⟨hn, hall⟩ u hu
      by_contra hg
      exact hn (fun i => by
        by_cases hij : i = j
        · subst hij; exact ⟨u, hu, hg⟩
        · exact hall i hij)
    · intro hA
      refine ⟨fun hall => ?_, fun i hij => ?_⟩
      · obtain ⟨u, hu, hg⟩ := hall j; exact hg (hA u hu)
      · by_contra hc
        push Not at hc
        exact hij (hsp v w hvw i j (hc v hv) (hc w hw) (hA v hv) (hA w hw))
  · have hB : B0 ↔ T1 := by tauto
    have e : ((¬T2 ∧ ¬B0) ∨ ((¬T2 ∧ ∃ u ∈ x, g u j) ∨
      ((T2 ∧ (¬T2 ∨ ¬B0)) ∧ (∀ i : Fin m, i ≠ j → ∃ u ∈ x, ¬ g u i)))) ↔
        (¬ T1 ∨ ∃ u ∈ x, g u j) := by
      rw [hB]; simp only [h2, not_false_eq_true, true_and, false_and, or_false]
    rw [e, hT1]
    have huniq : ∀ v ∈ x, ∀ w ∈ x, v = w := by
      intro v hv w hw; by_contra h; exact h2 (hT2.mpr ⟨v, hv, w, hw, h⟩)
    constructor
    · rintro (h | ⟨u, hu, hg⟩) v hv
      · exact absurd ⟨v, hv⟩ h
      · rw [huniq v hv u hu]; exact hg
    · intro hA
      by_cases h1 : ∃ v, v ∈ x
      · obtain ⟨v, hv⟩ := h1; exact Or.inr ⟨v, hv, hA v hv⟩
      · exact Or.inl h1

lemma sum_range_map (c : ℕ → ℕ) (m : ℕ) :
    ((List.range m).map c).sum = ∑ i ∈ Finset.range m, c i := by
  induction m with
  | zero => simp
  | succ m ih => simp [List.range_succ, Finset.sum_range_succ, ih]

noncomputable def rr {n m : ℕ} (g : Fin n → Fin m → Prop) (i : ℕ) : ℕ :=
  if h : i < m then (Finset.univ.filter (fun u : Fin n => g u ⟨i, h⟩)).card else 0

theorem build (n m : ℕ) (g : Fin n → Fin m → Prop)
    (hsp : ∀ u v : Fin n, u ≠ v → ∀ j j' : Fin m, g u j → g v j → g u j' → g v j' → j = j') :
    ∃ gs : List Gate, ∃ tap : ℕ → ℕ, Good (n+2) gs ∧ nc gs = 2 ∧
      gs.length ≤ Nat.log2 n * n + 3 * n + 3 * (∑ i ∈ Finset.range m, rr g i) + 11 * m + 12 ∧
      ∀ j : Fin m, Rep (n+2) (env n) gs (tap j.val) (fun x => ∀ u ∈ x, g u j) := by
  have hN := env_len n
  have G0 : Good (n+2) ([] : List Gate) := fun j h => by simp at h
  have hsumc : ((List.range m).map (fun i => 2 * rr g i + 3)).sum =
      2 * (∑ i ∈ Finset.range m, rr g i) + 3 * m := by
    rw [sum_range_map, Finset.sum_add_distrib, ← Finset.mul_sum]; simp; ring
  have hsumM : ((List.range m).map (fun i => rr g i + 1)).sum =
      (∑ i ∈ Finset.range m, rr g i) + m := by
    rw [sum_range_map, Finset.sum_add_distrib]; simp
  have hsum5 : ((List.range m).map (fun _ => 5)).sum = 5 * m := by
    rw [sum_range_map]; simp; ring
  generalize (∑ i ∈ Finset.range m, rr g i) = S at *

  obtain ⟨h1, tab, gd, n1, l1, T⟩ := table n (Nat.log2 n) [] G0
  simp only [List.nil_append] at gd T

  obtain ⟨h2, wT1, gd, n2, l2, RT1⟩ := t1_step gd T le_rfl
  replace T := TabOK_ext n T h2
  have L2 := List.length_append (as := h1) (bs := h2)
  have N2 := nc_append h1 h2
  generalize h1 ++ h2 = G at *

  obtain ⟨h3, wT2, gd, n3, l3, RT2⟩ := t2_step gd T le_rfl
  replace T := TabOK_ext n T h3
  replace RT1 := Rep_ext hN RT1 h3
  have L3 := List.length_append (as := G) (bs := h3)
  have N3 := nc_append G h3
  generalize G ++ h3 = G' at *

  let QD : ℕ → Finset (Fin n) → Prop := fun i x => ∀ h : i < m, ∃ u ∈ x, ¬ g u ⟨i, h⟩
  obtain ⟨h4, fD, gd, n4, l4, RD⟩ := family hN (List.range m) (fun i => 2 * rr g i + 3) QD
    (fun G => TabOK n G (Nat.log2 n) tab) (fun G hs h => TabOK_ext n h hs) (by
      intro i _ G hG hT
      by_cases him : i < m
      · obtain ⟨hs, w, a1, a2, a3, a4⟩ := dead_step g hG hT le_rfl ⟨i, him⟩
        refine ⟨hs, w, a1, a2, ?_, Rep_congr a4 (fun x => by simp [QD, him])⟩
        rw [show rr g i = (Finset.univ.filter (fun u : Fin n => g u ⟨i, him⟩)).card by simp [rr, him]]
        exact a3
      · obtain ⟨hs, w, a1, a2, a3, a4⟩ := ext_true hN hG
        exact ⟨hs, w, a1, a2, by omega, Rep_congr a4 (fun x => by simp [QD, him])⟩) G' gd T
  replace RT1 := Rep_ext hN RT1 h4
  replace RT2 := Rep_ext hN RT2 h4
  have L4 := List.length_append (as := G') (bs := h4)
  have N4 := nc_append G' h4
  clear T
  generalize G' ++ h4 = G at *

  let QM : ℕ → Finset (Fin n) → Prop := fun i x => ∀ h : i < m, ∃ u ∈ x, g u ⟨i, h⟩
  obtain ⟨h5, fM, gd, n5, l5, RM⟩ := family hN (List.range m) (fun i => rr g i + 1) QM
    (fun _ => True) (fun _ _ _ => trivial) (by
      intro i _ G hG _
      by_cases him : i < m
      · obtain ⟨hs, w, a1, a2, a3, a4⟩ := marked_step g hG ⟨i, him⟩
        refine ⟨hs, w, a1, a2, ?_, Rep_congr a4 (fun x => by simp [QM, him])⟩
        rw [show rr g i = (Finset.univ.filter (fun u : Fin n => g u ⟨i, him⟩)).card by simp [rr, him]]
        exact a3
      · obtain ⟨hs, w, a1, a2, a3, a4⟩ := ext_true hN hG
        exact ⟨hs, w, a1, a2, by omega, Rep_congr a4 (fun x => by simp [QM, him])⟩) G gd trivial
  replace RT1 := Rep_ext hN RT1 h5
  replace RT2 := Rep_ext hN RT2 h5
  replace RD := fun i hi => Rep_ext hN (RD i hi) h5
  have L5 := List.length_append (as := G) (bs := h5)
  have N5 := nc_append G h5
  generalize G ++ h5 = G' at *

  obtain ⟨h6, pD, gd, n6, l6, RP⟩ := scan hN gd m fD QD (fun i hi => RD i (List.mem_range.mpr hi))
  replace RT1 := Rep_ext hN RT1 h6
  replace RT2 := Rep_ext hN RT2 h6
  replace RD := fun i hi => Rep_ext hN (RD i hi) h6
  replace RM := fun i hi => Rep_ext hN (RM i hi) h6
  have L6 := List.length_append (as := G') (bs := h6)
  have N6 := nc_append G' h6
  generalize G' ++ h6 = G at *

  obtain ⟨h7, sD, gd, n7, l7, RS⟩ := scan hN gd m (fun i => fD (m - 1 - i)) (fun i => QD (m - 1 - i))
    (fun i hi => RD _ (List.mem_range.mpr (by omega)))
  replace RT1 := Rep_ext hN RT1 h7
  replace RT2 := Rep_ext hN RT2 h7
  replace RM := fun i hi => Rep_ext hN (RM i hi) h7
  replace RP := fun k hk => Rep_ext hN (RP k hk) h7
  have L7 := List.length_append (as := G) (bs := h7)
  have N7 := nc_append G h7
  clear RD
  generalize G ++ h7 = G' at *

  obtain ⟨h8, wT3, gd, n8, l8, RT3⟩ := ext_and2 hN gd RT2 (RP m le_rfl)
  replace RT1 := Rep_ext hN RT1 h8
  replace RT2 := Rep_ext hN RT2 h8
  replace RM := fun i hi => Rep_ext hN (RM i hi) h8
  replace RP := fun k hk => Rep_ext hN (RP k hk) h8
  replace RS := fun k hk => Rep_ext hN (RS k hk) h8
  have L8 := List.length_append (as := G') (bs := h8)
  have N8 := nc_append G' h8
  generalize G' ++ h8 = G at *

  obtain ⟨gd, n9, Rnb1⟩ := rep_not hN gd RT2
  replace RT1 := Rep_ext hN RT1 [⟨GateOp.not, [wT2]⟩]
  replace RT2 := Rep_ext hN RT2 [⟨GateOp.not, [wT2]⟩]
  replace RT3 := Rep_ext hN RT3 [⟨GateOp.not, [wT2]⟩]
  replace RM := fun i hi => Rep_ext hN (RM i hi) [⟨GateOp.not, [wT2]⟩]
  replace RP := fun k hk => Rep_ext hN (RP k hk) [⟨GateOp.not, [wT2]⟩]
  replace RS := fun k hk => Rep_ext hN (RS k hk) [⟨GateOp.not, [wT2]⟩]
  have L9 := List.length_append (as := G) (bs := [⟨GateOp.not, [wT2]⟩])
  have N9 := nc_append G [⟨GateOp.not, [wT2]⟩]
  generalize n + 2 + G.length = wnb1 at Rnb1
  generalize G ++ [⟨GateOp.not, [wT2]⟩] = G' at *

  obtain ⟨h10, wa, gd, n10, l10, Ra⟩ := ext_and2 hN gd RT1 Rnb1
  obtain ⟨h11, wb0, gd, n11, l11, Rb0⟩ := ext_or2 hN gd Ra (Rep_ext hN RT3 h10)
  replace RT2 := Rep_ext hN (Rep_ext hN RT2 h10) h11
  replace Rnb1 := Rep_ext hN (Rep_ext hN Rnb1 h10) h11
  replace RM := fun i hi => Rep_ext hN (Rep_ext hN (RM i hi) h10) h11
  replace RP := fun k hk => Rep_ext hN (Rep_ext hN (RP k hk) h10) h11
  replace RS := fun k hk => Rep_ext hN (Rep_ext hN (RS k hk) h10) h11
  have L10 := List.length_append (as := G') (bs := h10)
  have N10 := nc_append G' h10
  have L11 := List.length_append (as := G' ++ h10) (bs := h11)
  have N11 := nc_append (G' ++ h10) h11
  clear Ra RT1 RT3
  generalize G' ++ h10 = G at *
  generalize G ++ h11 = G'' at *

  obtain ⟨gd, n12, Rnb0⟩ := rep_not hN gd Rb0
  replace RT2 := Rep_ext hN RT2 [⟨GateOp.not, [wb0]⟩]
  replace Rnb1 := Rep_ext hN Rnb1 [⟨GateOp.not, [wb0]⟩]
  replace RM := fun i hi => Rep_ext hN (RM i hi) [⟨GateOp.not, [wb0]⟩]
  replace RP := fun k hk => Rep_ext hN (RP k hk) [⟨GateOp.not, [wb0]⟩]
  replace RS := fun k hk => Rep_ext hN (RS k hk) [⟨GateOp.not, [wb0]⟩]
  have L12 := List.length_append (as := G'') (bs := [⟨GateOp.not, [wb0]⟩])
  have N12 := nc_append G'' [⟨GateOp.not, [wb0]⟩]
  generalize n + 2 + G''.length = wnb0 at Rnb0
  clear Rb0
  generalize G'' ++ [⟨GateOp.not, [wb0]⟩] = G at *

  obtain ⟨h13, wnt1, gd, n13, l13, Rnt1⟩ := ext_and2 hN gd Rnb1 Rnb0
  obtain ⟨h14, wnt3, gd, n14, l14, Rnt3⟩ := ext_or2 hN gd (Rep_ext hN Rnb1 h13) (Rep_ext hN Rnb0 h13)
  obtain ⟨h15, wq, gd, n15, l15, Rq⟩ := ext_and2 hN gd (Rep_ext hN (Rep_ext hN RT2 h13) h14) Rnt3
  have L13 := List.length_append (as := G) (bs := h13)
  have N13 := nc_append G h13
  have L14 := List.length_append (as := G ++ h13) (bs := h14)
  have N14 := nc_append (G ++ h13) h14
  have L15 := List.length_append (as := G ++ h13 ++ h14) (bs := h15)
  have N15 := nc_append (G ++ h13 ++ h14) h15
  replace Rnb1 := Rep_ext hN (Rep_ext hN (Rep_ext hN Rnb1 h13) h14) h15
  replace Rnt1 := Rep_ext hN (Rep_ext hN Rnt1 h14) h15
  replace RM := fun i hi => Rep_ext hN (Rep_ext hN (Rep_ext hN (RM i hi) h13) h14) h15
  replace RP := fun k hk => Rep_ext hN (Rep_ext hN (Rep_ext hN (RP k hk) h13) h14) h15
  replace RS := fun k hk => Rep_ext hN (Rep_ext hN (Rep_ext hN (RS k hk) h13) h14) h15
  clear Rnt3 RT2 Rnb0
  generalize G ++ h13 = G' at *
  generalize G' ++ h14 = G'' at *
  generalize G'' ++ h15 = G at *

  let T1 : Finset (Fin n) → Prop := fun x => ∃ v, v ∈ x
  let T2 : Finset (Fin n) → Prop := fun x => ∃ v ∈ x, ∃ w ∈ x, v ≠ w
  let AD : Finset (Fin n) → Prop := fun x => ∀ i < m, QD i x
  let B0 : Finset (Fin n) → Prop := fun x => (T1 x ∧ ¬ T2 x) ∨ (T2 x ∧ AD x)
  have Rnb1' : Rep (n+2) (env n) G wnb1 (fun x => ¬ T2 x) := Rnb1
  have Rnt1' : Rep (n+2) (env n) G wnt1 (fun x => ¬ T2 x ∧ ¬ B0 x) := Rnt1
  have Rq' : Rep (n+2) (env n) G wq (fun x => T2 x ∧ (¬ T2 x ∨ ¬ B0 x)) := Rq
  clear Rnb1 Rnt1 Rq
  obtain ⟨h16, fO, gd, n16, l16, RO⟩ := family hN (List.range m) (fun _ => 5)
    (fun i x => ∀ h : i < m, ∀ u ∈ x, g u ⟨i, h⟩)
    (fun G => Rep (n+2) (env n) G wnb1 (fun x => ¬ T2 x) ∧
      (∀ i ∈ List.range m, Rep (n+2) (env n) G (fM i) (QM i)) ∧
      (∀ k ≤ m, Rep (n+2) (env n) G (pD k) (fun x => ∀ i < k, QD i x)) ∧
      (∀ k ≤ m, Rep (n+2) (env n) G (sD k) (fun x => ∀ i < k, QD (m - 1 - i) x)) ∧
      Rep (n+2) (env n) G wq (fun x => T2 x ∧ (¬ T2 x ∨ ¬ B0 x)) ∧
      Rep (n+2) (env n) G wnt1 (fun x => ¬ T2 x ∧ ¬ B0 x))
    (fun G hs ⟨a, b, c, d, e, f⟩ => ⟨Rep_ext hN a hs, fun i hi => Rep_ext hN (b i hi) hs,
      fun k hk => Rep_ext hN (c k hk) hs, fun k hk => Rep_ext hN (d k hk) hs,
      Rep_ext hN e hs, Rep_ext hN f hs⟩) (by
      intro i hi G hG ⟨P1, PM, PP, PS, Pq, Pt⟩
      by_cases him : i < m
      · obtain ⟨a, w1, g1, c1, l1, R1⟩ := ext_and2 hN hG P1 (PM i hi)
        obtain ⟨b, w2, g2, c2, l2, R2⟩ := ext_and2 hN g1 (Rep_ext hN (PP i him.le) a)
          (Rep_ext hN (PS (m - 1 - i) (by omega)) a)
        obtain ⟨c, w3, g3, c3, l3, R3⟩ := ext_and2 hN g2 (Rep_ext hN (Rep_ext hN Pq a) b) R2
        obtain ⟨d, w4, g4, c4, l4, R4⟩ := ext_or2 hN g3 (Rep_ext hN (Rep_ext hN R1 b) c) R3
        obtain ⟨e, w5, g5, c5, l5, R5⟩ := ext_or2 hN g4
          (Rep_ext hN (Rep_ext hN (Rep_ext hN (Rep_ext hN Pt a) b) c) d) R4
        refine ⟨a ++ b ++ c ++ d ++ e, w5, by simpa using g5,
          by simp only [nc_append]; omega, by simp; omega, ?_⟩
        have R5' := R5
        simp only [List.append_assoc] at R5' ⊢
        refine Rep_congr R5' (fun x => ?_)
        have hl := logic g hsp x ⟨i, him⟩ (T1 x) (T2 x) (AD x) (B0 x) Iff.rfl Iff.rfl (by
          simp only [AD, QD]
          constructor
          · intro h j; exact h j.val j.2 j.2
          · intro h k hk _; exact h ⟨k, hk⟩) Iff.rfl
        have hM : QM i x ↔ ∃ u ∈ x, g u ⟨i, him⟩ := by simp [QM, him]
        have hPS : ((∀ k < i, QD k x) ∧ (∀ k < m - 1 - i, QD (m - 1 - k) x)) ↔
            ∀ j : Fin m, j ≠ ⟨i, him⟩ → ∃ u ∈ x, ¬ g u j := by
          simp only [QD]
          constructor
          · rintro ⟨h1, h2⟩ j hj
            have hj' : j.val ≠ i := fun e => hj (Fin.ext e)
            rcases Nat.lt_or_gt_of_ne hj' with h | h
            · exact h1 j.val h j.2
            · have := h2 (m - 1 - j.val) (by omega) (by omega)
              have e : m - 1 - (m - 1 - j.val) = j.val := by omega
              simp only [e] at this
              exact this
          · intro h
            refine ⟨fun k hk hkm => h ⟨k, hkm⟩ (fun e => by simp at e; omega),
              fun k hk hkm => h ⟨m - 1 - k, hkm⟩ (fun e => by simp at e; omega)⟩
        rw [← hM, ← hPS] at hl
        simp only [him, forall_true_left]
        rw [← hl]
      · obtain ⟨hs, w, a1, a2, a3, a4⟩ := ext_true hN hG
        exact ⟨hs, w, a1, a2, by omega, Rep_congr a4 (fun x => by simp [him])⟩)
    G gd ⟨Rnb1', RM, RP, RS, Rq', Rnt1'⟩
  refine ⟨G ++ h16, fO, gd, ?_, ?_, fun j => Rep_congr (RO j.val (List.mem_range.mpr j.2))
    (fun x => by simp [j.2])⟩
  · rw [nc_append]; omega
  · rw [hsumc] at l4; rw [hsumM] at l5; rw [hsum5] at l16
    simp only [List.length_append, List.length_singleton] at *
    omega

end Main
end PEqualNP.Outside.L_meta_49529_aux

theorem PEqualNP.Outside.L_meta_49529 : (letI : ∀ p : Prop, Decidable p := Classical.propDecidable
∀ (n m : Nat) (g : Fin n → Fin m → Prop),
  let cols := fun (u : Fin n) => Finset.univ.filter (g u)
  let s := Finset.univ.sum (fun u => (cols u).card)
  (∀ u v, u ≠ v → ((cols u) ∩ (cols v)).card ≤ 1) →
  ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin m → Fin (n+2+C.size)),
    PEqualNP.MetaComplexity.FanInTwo C ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧ C.output < n+2+C.size ∧
    PEqualNP.NotBracket.notCount C ≤ 2 ∧
    C.size ≤ 32*((n+1)*(Nat.log2 (n+1)+1)+m+s+1) ∧
    ∀ x : Finset (Fin n),
      let input := List.ofFn (fun u : Fin n => decide (u ∈ x)) ++ [false,true]
      ∀ j : Fin m, (C.wires input).getD (tap j).val false = decide (∀ u ∈ x, g u j)) := by
  intro n m g cols s hcap
  have hsp : ∀ u v : Fin n, u ≠ v → ∀ j j' : Fin m, g u j → g v j → g u j' → g v j' → j = j' := by
    intro u v huv j j' h1 h2 h3 h4
    have hc := hcap u v huv
    rw [Finset.card_le_one] at hc
    exact hc j (by simp [cols, h1, h2]) j' (by simp [cols, h3, h4])
  obtain ⟨gs, tap, hG, hnc, hlen, hR⟩ := L_meta_49529_aux.build n m g hsp
  refine ⟨⟨gs, 0⟩, fun j => ⟨tap j.val, (hR j).1⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g' hg'
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hg'
    obtain ⟨h1, h2, _⟩ := hG k hk
    refine ⟨?_, h2⟩
    rcases h1 with h | h | h <;> simp [h]
  · intro k hk i hi
    simp only [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem _ _ hk] at hi
    exact (hG k hk).2.2 i hi
  · show 0 < n + 2 + gs.length; omega
  · unfold PEqualNP.NotBracket.notCount
    show (gs.filter _).length ≤ 2
    rw [List.filter_congr (q := fun g => L_meta_49529_aux.isNot g.op) (fun g _ => by
      cases h : g.op <;> simp [L_meta_49529_aux.isNot])]
    unfold L_meta_49529_aux.nc at hnc
    omega
  · show gs.length ≤ _
    have hs : ∑ i ∈ Finset.range m, L_meta_49529_aux.rr g i = s := by
      rw [← Fin.sum_univ_eq_sum_range]
      simp only [s, cols, L_meta_49529_aux.rr, Fin.is_lt, ↓reduceDIte, Fin.eta]
      simp only [Finset.card_filter]
      rw [Finset.sum_comm]
    have hK : Nat.log2 n * n ≤ (n + 1) * Nat.log2 (n + 1) := by
      have : Nat.log2 n ≤ Nat.log2 (n+1) := by
        rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]; exact Nat.log_mono_right (by omega)
      calc Nat.log2 n * n ≤ Nat.log2 (n+1) * (n+1) := Nat.mul_le_mul this (by omega)
        _ = (n + 1) * Nat.log2 (n + 1) := by ring
    have e : (n+1) * (Nat.log2 (n+1) + 1) = (n+1) * Nat.log2 (n+1) + n + 1 := by ring
    rw [e]
    rw [hs] at hlen
    omega
  · intro x input j
    have hin : input = L_meta_49529_aux.env n x := by
      simp only [input, L_meta_49529_aux.env]
    show (L_meta_49529_aux.W gs input).getD (tap j.val) false = _
    rw [hin, Bool.eq_iff_iff]
    simp only [decide_eq_true_iff]
    exact (hR j).2 x
