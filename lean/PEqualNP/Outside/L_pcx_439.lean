import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_pcx_439
def par {l : ℕ} (s : Fin l → Bool) : Bool :=
  decide ((Finset.univ.filter (fun p => s p = true)).card % 2 = 1)
def visF {a h l : ℕ} (u : (Fin h → Bool) × (Fin (a+3) → Fin h → Fin l → Bool))
    (i : Fin (a+3)) (b : Fin h) : Bool :=
  xor (u.1 b) (par (u.2 i b))
def mkU {a h l : ℕ} (V : Fin (a+3) → Fin h → Bool) (i : Fin (a+3))
    (t : Fin h → Fin l → Bool) :
    (Fin h → Bool) × (Fin (a+3) → Fin h → Fin l → Bool) :=
  (fun b => xor (V i b) (par (t b)),
   fun e => if e = i then t else
     fun b q => decide (q.val = 0) && xor (V e b) (xor (V i b) (par (t b))))
theorem par_single {l : ℕ} (hl : 0 < l) (β : Bool) :
    par (fun q : Fin l => decide (q.val = 0) && β) = β := by
  unfold par
  cases β
  · simp
  · have : (Finset.univ.filter (fun q : Fin l => (decide (q.val = 0) && true) = true))
        = {⟨0, hl⟩} := by
      ext q
      simp [Fin.ext_iff]
    rw [this]
    simp
theorem vis_mkU {a h l : ℕ} (hl : 0 < l) (V : Fin (a+3) → Fin h → Bool) (i : Fin (a+3))
    (t : Fin h → Fin l → Bool) : visF (mkU V i t) = V := by
  funext e b
  unfold visF mkU
  by_cases he : e = i
  · subst he
    simp
  · dsimp only
    rw [if_neg he, par_single hl]
    cases V e b <;> cases V i b <;> cases par (t b) <;> rfl
theorem mkU_snd {a h l : ℕ} (V : Fin (a+3) → Fin h → Bool) (i : Fin (a+3))
    (t : Fin h → Fin l → Bool) : (mkU V i t).2 i = t := by
  unfold mkU
  simp
theorem exists_viol {a : ℕ} (charge : Fin (a+3) → Bool)
    (hch : (Finset.univ.filter (fun i => charge i = true)).card % 2 = 1)
    (x : Fin (a+3) → Bool) : ∃ e, xor (x e) (x (e+1)) ≠ charge e := by
  by_contra hcon
  push_neg at hcon
  let g : Bool → ZMod 2 := fun b => if b then 1 else 0
  have hg : ∀ p q : Bool, g (xor p q) = g p + g q := by
    intro p q
    cases p <;> cases q <;> decide
  have h1 : ((Finset.univ.filter (fun i => charge i = true)).card : ZMod 2) = 1 := by
    rw [← ZMod.natCast_mod, hch]
    rfl
  have h2 : ((Finset.univ.filter (fun i => charge i = true)).card : ZMod 2)
      = ∑ e, g (charge e) := by
    rw [Finset.card_filter]
    push_cast
    rfl
  have h3 : ∑ e, g (charge e) = ∑ e, g (x e) + ∑ e, g (x (e+1)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e _
    rw [← hcon e, hg]
  have h4 : ∑ e : Fin (a+3), g (x (e+1)) = ∑ e, g (x e) :=
    Fintype.sum_equiv (Equiv.addRight 1) _ _ (fun e => rfl)
  have h5 : ∀ s : ZMod 2, s + s = 0 := by decide
  have h6 : (1 : ZMod 2) = 0 := by
    rw [← h1, h2, h3, h4, h5]
  exact absurd h6 (by decide)
theorem uniq_viol_last {a : ℕ} (charge : Fin (a+3) → Bool)
    (hch : (Finset.univ.filter (fun i => charge i = true)).card % 2 = 1) :
    ∃ x : Fin (a+3) → Bool, ∀ e, xor (x e) (x (e+1)) ≠ charge e ↔ e + 1 = 0 := by
  let f : ℕ → ℕ := fun s => if hs : s < a + 3 then (if charge ⟨s, hs⟩ then 1 else 0) else 0
  have htot : ∑ s ∈ Finset.range (a+3), f s
      = (Finset.univ.filter (fun i => charge i = true)).card := by
    rw [Finset.card_filter, ← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i _
    simp [f, i.isLt]
  refine ⟨fun e => decide ((∑ s ∈ Finset.range e.val, f s) % 2 = 1), ?_⟩
  intro e
  have hv := Fin.val_add_one e
  by_cases he : e = Fin.last (a+2)
  · rw [if_pos he] at hv
    have h0 : e + 1 = 0 := Fin.ext (by rw [hv]; rfl)
    simp only [h0, iff_true]
    have hA : (∑ s ∈ Finset.range ((0 : Fin (a+3)) : ℕ), f s) = 0 := by simp
    have hev : e.val = a + 2 := by subst he; rfl
    have hs : ∑ s ∈ Finset.range (a+3), f s = ∑ s ∈ Finset.range (a+2), f s + f (a+2) :=
      Finset.sum_range_succ f (a+2)
    have hfe : f (a+2) = if charge e = true then 1 else 0 := by
      subst he
      simp only [f, dif_pos (show a + 2 < a + 3 by omega)]
      rfl
    rw [hA, hev]
    rw [htot, hfe] at hs
    rcases Nat.mod_two_eq_zero_or_one (∑ s ∈ Finset.range (a+2), f s) with hS | hS
    · cases hc : charge e
      · rw [hc] at hs
        simp at hs
        omega
      · simp [hS]
    · cases hc : charge e
      · simp [hS]
      · rw [hc] at hs
        simp at hs
        omega
  · rw [if_neg he] at hv
    have h0 : ¬ (e + 1 = 0) := by
      intro h
      have := congrArg Fin.val h
      rw [hv] at this
      simp at this
    simp only [h0, iff_false, not_not]
    rw [hv, Finset.sum_range_succ]
    have hfe : f e.val = if charge e then 1 else 0 := by
      simp [f, e.isLt]
    rw [hfe]
    cases charge e
    · simp
    · simp only [if_true]
      rcases Nat.mod_two_eq_zero_or_one (∑ s ∈ Finset.range e.val, f s) with h | h
      · have : (∑ s ∈ Finset.range e.val, f s + 1) % 2 = 1 := by omega
        simp [h, this]
      · have : (∑ s ∈ Finset.range e.val, f s + 1) % 2 = 0 := by omega
        simp [h, this]
theorem uniq_viol {a : ℕ} (charge : Fin (a+3) → Bool)
    (hch : (Finset.univ.filter (fun i => charge i = true)).card % 2 = 1) (i : Fin (a+3)) :
    ∃ x : Fin (a+3) → Bool, ∀ e, xor (x e) (x (e+1)) ≠ charge e ↔ e = i := by
  have hch' : (Finset.univ.filter (fun e => charge (e + (i+1)) = true)).card % 2 = 1 := by
    have : (Finset.univ.filter (fun e => charge (e + (i+1)) = true)).card
        = (Finset.univ.filter (fun e => charge e = true)).card := by
      rw [Finset.card_filter, Finset.card_filter]
      exact Fintype.sum_equiv (Equiv.addRight (i+1)) _ _ (fun e => rfl)
    rw [this]
    exact hch
  obtain ⟨x', hx'⟩ := uniq_viol_last (fun e => charge (e + (i+1))) hch'
  refine ⟨fun e => x' (e - (i+1)), fun e => ?_⟩
  have h1 : e + 1 - (i + 1) = e - (i+1) + 1 := by abel
  have h2 : charge e = charge (e - (i+1) + (i+1)) := by rw [sub_add_cancel]
  have h3 : e - (i+1) + 1 = 0 ↔ e = i := by
    rw [show e - (i+1) + 1 = e - i by abel, sub_eq_zero]
  dsimp only
  rw [h1, h2]
  rw [hx' (e - (i+1))]
  exact h3
def Phi {a h d : ℕ} (slot : Fin (a+3) → Fin h ↪ Fin d)
    (first : Fin d → (Fin (a+3) → Bool) → (Fin (a+3) → Fin h → Bool) → Bool)
    (x : Fin (a+3) → Bool) (V : Fin (a+3) → Fin h → Bool) : Fin d → Bool :=
  fun p => first p x (fun i b => decide (slot i b = p) && V i b)
def Valid {a h l d k : ℕ} (charge : Fin (a+3) → Bool) (slot : Fin (a+3) → Fin h ↪ Fin d)
    (first : Fin d → (Fin (a+3) → Bool) → (Fin (a+3) → Fin h → Bool) → Bool)
    (last : (Fin d → Bool) → (Fin (a+3) → Bool) →
      ((Fin h → Bool) × (Fin (a+3) → Fin h → Fin l → Bool)) → Fin k → Bool)
    (out : (Fin d → Bool) → (Fin k → Bool) → Fin (a+3) × (Fin h → Bool) × (Fin h → Fin l → Bool)) :
    Prop :=
  ∀ x u, let z : Fin d → Bool := Phi slot first x (visF u)
    let ans := out z (last z x u)
    xor (x ans.1) (x (ans.1+1)) ≠ charge ans.1 ∧ ans.2.1 = visF u ans.1 ∧ ans.2.2 = u.2 ans.1
theorem core {a h l d k : ℕ} (hl : 0 < l) {charge : Fin (a+3) → Bool}
    {slot : Fin (a+3) → Fin h ↪ Fin d}
    {first : Fin d → (Fin (a+3) → Bool) → (Fin (a+3) → Fin h → Bool) → Bool}
    {last : (Fin d → Bool) → (Fin (a+3) → Bool) →
      ((Fin h → Bool) × (Fin (a+3) → Fin h → Fin l → Bool)) → Fin k → Bool}
    {out : (Fin d → Bool) → (Fin k → Bool) → Fin (a+3) × (Fin h → Bool) × (Fin h → Fin l → Bool)}
    (hv : Valid charge slot first last out)
    (x : Fin (a+3) → Bool) (i : Fin (a+3)) (hx : ∀ e, xor (x e) (x (e+1)) ≠ charge e ↔ e = i)
    (V : Fin (a+3) → Fin h → Bool) (t : Fin h → Fin l → Bool) :
    out (Phi slot first x V) (last (Phi slot first x V) x (mkU V i t)) = (i, V i, t) := by
  have H := hv x (mkU V i t)
  rw [vis_mkU hl] at H
  dsimp only at H
  obtain ⟨h1, h2, h3⟩ := H
  have hi := (hx _).mp h1
  rw [hi] at h2 h3
  rw [mkU_snd] at h3
  exact Prod.ext hi (Prod.ext h2 h3)
theorem card_T (h l : ℕ) : Fintype.card (Fin h → Fin l → Bool) = 2 ^ (h * l) := by
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  rw [← pow_mul, mul_comm]
theorem lower_hl {a h l d k : ℕ} (hl : 0 < l) {charge : Fin (a+3) → Bool}
    (hch : (Finset.univ.filter (fun i => charge i = true)).card % 2 = 1)
    {slot : Fin (a+3) → Fin h ↪ Fin d}
    {first : Fin d → (Fin (a+3) → Bool) → (Fin (a+3) → Fin h → Bool) → Bool}
    {last : (Fin d → Bool) → (Fin (a+3) → Bool) →
      ((Fin h → Bool) × (Fin (a+3) → Fin h → Fin l → Bool)) → Fin k → Bool}
    {out : (Fin d → Bool) → (Fin k → Bool) → Fin (a+3) × (Fin h → Bool) × (Fin h → Fin l → Bool)}
    (hv : Valid charge slot first last out) : h * l ≤ k := by
  obtain ⟨x, hx⟩ := uniq_viol charge hch 0
  let V0 : Fin (a+3) → Fin h → Bool := fun _ _ => false
  let g : (Fin h → Fin l → Bool) → (Fin k → Bool) :=
    fun t => last (Phi slot first x V0) x (mkU V0 0 t)
  have hg : Function.Injective g := by
    intro t t' htt
    have e1 := core hl hv x 0 hx V0 t
    have e2 := core hl hv x 0 hx V0 t'
    simp only [g] at htt
    rw [htt, e2] at e1
    simp only [Prod.mk.injEq] at e1
    exact e1.2.2.symm
  have h1 := Fintype.card_le_of_injective g hg
  rw [card_T] at h1
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at h1
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h1
theorem cond_C {a h l d k : ℕ} (hl : 0 < l) {charge : Fin (a+3) → Bool}
    {slot : Fin (a+3) → Fin h ↪ Fin d}
    {first : Fin d → (Fin (a+3) → Bool) → (Fin (a+3) → Fin h → Bool) → Bool}
    {last : (Fin d → Bool) → (Fin (a+3) → Bool) →
      ((Fin h → Bool) × (Fin (a+3) → Fin h → Fin l → Bool)) → Fin k → Bool}
    {out : (Fin d → Bool) → (Fin k → Bool) → Fin (a+3) × (Fin h → Bool) × (Fin h → Fin l → Bool)}
    (hv : Valid charge slot first last out) (hk : k = h * l)
    (x x' : Fin (a+3) → Bool) (i j : Fin (a+3))
    (hx : ∀ e, xor (x e) (x (e+1)) ≠ charge e ↔ e = i)
    (hx' : ∀ e, xor (x' e) (x' (e+1)) ≠ charge e ↔ e = j)
    (V V' : Fin (a+3) → Fin h → Bool)
    (hz : Phi slot first x V = Phi slot first x' V') : i = j ∧ V i = V' j := by
  let g : (Fin h → Fin l → Bool) → (Fin k → Bool) :=
    fun t => last (Phi slot first x V) x (mkU V i t)
  have hg : Function.Injective g := by
    intro t t' htt
    have e1 := core hl hv x i hx V t
    have e2 := core hl hv x i hx V t'
    simp only [g] at htt
    rw [htt, e2] at e1
    simp only [Prod.mk.injEq] at e1
    exact e1.2.2.symm
  have hcard : Fintype.card (Fin h → Fin l → Bool) = Fintype.card (Fin k → Bool) := by
    rw [card_T]
    simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    rw [hk]
  have hbij := (Fintype.bijective_iff_injective_and_card g).mpr ⟨hg, hcard⟩
  let t0 : Fin h → Fin l → Bool := fun _ _ => false
  obtain ⟨t, ht⟩ := hbij.2 (last (Phi slot first x' V') x' (mkU V' j t0))
  have e1 := core hl hv x i hx V t
  have e2 := core hl hv x' j hx' V' t0
  rw [← hz] at e2 ht
  simp only [g] at ht
  rw [ht, e2] at e1
  simp only [Prod.mk.injEq] at e1
  exact ⟨e1.1.symm, e1.2.1.symm⟩
def single {a h : ℕ} (i : Fin (a+3)) (w : Fin h → Bool) : Fin (a+3) → Fin h → Bool :=
  fun e b' => decide (e = i) && w b'
theorem dep_only {a h d : ℕ} (slot : Fin (a+3) → Fin h ↪ Fin d)
    (first : Fin d → (Fin (a+3) → Bool) → (Fin (a+3) → Fin h → Bool) → Bool)
    (x : Fin (a+3) → Bool) (i : Fin (a+3)) (w : Fin h → Bool) (b : Fin h) :
    Phi slot first x (single i w) (slot i b) = Phi slot first x (single i (fun _ => w b)) (slot i b) := by
  unfold Phi single
  congr 1
  funext e b'
  by_cases he : e = i
  · subst he
    by_cases hb : b' = b
    · subst hb
      rfl
    · have : slot e b' ≠ slot e b := fun hh => hb ((slot e).injective hh)
      simp [this]
  · simp [he]
theorem outside {a h d : ℕ} (slot : Fin (a+3) → Fin h ↪ Fin d)
    (first : Fin d → (Fin (a+3) → Bool) → (Fin (a+3) → Fin h → Bool) → Bool)
    (x : Fin (a+3) → Bool) (i : Fin (a+3)) (w : Fin h → Bool) (q : Fin d)
    (hq : ∀ b, slot i b ≠ q) :
    Phi slot first x (single i w) q = Phi slot first x (fun _ _ => false) q := by
  unfold Phi single
  congr 1
  funext e b'
  by_cases he : e = i
  · subst he
    simp [hq b']
  · simp [he]
theorem flip_xor {a h d : ℕ} (slot : Fin (a+3) → Fin h ↪ Fin d)
    (first : Fin d → (Fin (a+3) → Bool) → (Fin (a+3) → Fin h → Bool) → Bool)
    (x : Fin (a+3) → Bool) (i : Fin (a+3))
    (HCi : ∀ V V', Phi slot first x V = Phi slot first x V' → V i = V' i) (b : Fin h) (β : Bool) :
    Phi slot first x (single i (fun _ => β)) (slot i b)
      = xor (Phi slot first x (single i (fun _ => false)) (slot i b)) β := by
  have hne : Phi slot first x (single i (fun _ => false)) (slot i b)
      ≠ Phi slot first x (single i (fun _ => true)) (slot i b) := by
    intro heq
    let w1 : Fin h → Bool := fun b' => decide (b' = b)
    have hall : Phi slot first x (single i (fun _ => false)) = Phi slot first x (single i w1) := by
      funext q
      by_cases hq : q = slot i b
      · subst hq
        rw [dep_only slot first x i w1 b]
        have : w1 b = true := by simp [w1]
        rw [this]
        exact heq
      · unfold Phi single
        congr 1
        funext e b'
        by_cases he : e = i
        · subst he
          by_cases hb : b' = b
          · subst hb
            have : slot e b' ≠ q := fun hh => hq hh.symm
            simp [this]
          · simp [w1, hb]
        · simp [he]
    have := congrFun (HCi _ _ hall) b
    simp [single, w1] at this
  cases β
  · cases Phi slot first x (single i (fun _ => false)) (slot i b) <;> rfl
  · revert hne
    generalize Phi slot first x (single i (fun _ => false)) (slot i b) = p0
    generalize Phi slot first x (single i (fun _ => true)) (slot i b) = p1
    cases p0 <;> cases p1 <;> simp
theorem realize {a h d : ℕ} (slot : Fin (a+3) → Fin h ↪ Fin d)
    (first : Fin d → (Fin (a+3) → Bool) → (Fin (a+3) → Fin h → Bool) → Bool)
    (x : Fin (a+3) → Bool) (i : Fin (a+3))
    (HCi : ∀ V V', Phi slot first x V = Phi slot first x V' → V i = V' i) (τ : Fin d → Bool) :
    ∃ w : Fin h → Bool, ∀ b, Phi slot first x (single i w) (slot i b) = τ (slot i b) := by
  refine ⟨fun b => xor (Phi slot first x (single i (fun _ => false)) (slot i b)) (τ (slot i b)),
    fun b => ?_⟩
  rw [dep_only slot first x i _ b]
  rw [flip_xor slot first x i HCi b]
  generalize Phi slot first x (single i (fun _ => false)) (slot i b) = p0
  generalize τ (slot i b) = t0
  cases p0 <;> cases t0 <;> rfl
theorem cond_D {a h d : ℕ} (slot : Fin (a+3) → Fin h ↪ Fin d)
    (first : Fin d → (Fin (a+3) → Bool) → (Fin (a+3) → Fin h → Bool) → Bool)
    (xs : Fin (a+3) → Fin (a+3) → Bool)
    (HC : ∀ i j V V', Phi slot first (xs i) V = Phi slot first (xs j) V' → i = j ∧ V i = V' j)
    (i j : Fin (a+3)) (hij : i ≠ j) :
    ∃ q, (∀ b, slot i b ≠ q) ∧ (∀ b, slot j b ≠ q) ∧
      Phi slot first (xs i) (fun _ _ => false) q ≠ Phi slot first (xs j) (fun _ _ => false) q := by
  classical
  by_contra hcon
  push_neg at hcon
  let τ : Fin d → Bool := fun q =>
    if ∃ b, slot i b = q then
      (if ∃ b, slot j b = q then false else Phi slot first (xs j) (fun _ _ => false) q)
    else Phi slot first (xs i) (fun _ _ => false) q
  obtain ⟨w, hw⟩ := realize slot first (xs i) i (fun V V' hh => (HC i i V V' hh).2) τ
  obtain ⟨w', hw'⟩ := realize slot first (xs j) j (fun V V' hh => (HC j j V V' hh).2) τ
  have e1 : Phi slot first (xs i) (single i w) = τ := by
    funext q
    by_cases hq : ∃ b, slot i b = q
    · obtain ⟨b, rfl⟩ := hq
      exact hw b
    · have hq2 : ∀ b, slot i b ≠ q := by
        intro b hb
        exact hq ⟨b, hb⟩
      rw [outside slot first (xs i) i w q hq2]
      simp only [τ]
      rw [if_neg hq]
  have e2 : Phi slot first (xs j) (single j w') = τ := by
    funext q
    by_cases hq : ∃ b, slot j b = q
    · obtain ⟨b, rfl⟩ := hq
      exact hw' b
    · have hq2 : ∀ b, slot j b ≠ q := by
        intro b hb
        exact hq ⟨b, hb⟩
      rw [outside slot first (xs j) j w' q hq2]
      simp only [τ]
      by_cases hq' : ∃ b, slot i b = q
      · rw [if_pos hq', if_neg hq]
      · rw [if_neg hq']
        have hq3 : ∀ b, slot i b ≠ q := by
          intro b hb
          exact hq' ⟨b, hb⟩
        exact (hcon q hq3 hq2).symm
  exact hij (HC i j _ _ (e1.trans e2.symm)).1
theorem card_mask {d : ℕ} (R : Finset (Fin d)) :
    (Finset.univ.filter (fun z : Fin d → Bool => ∀ q, q ∉ R → z q = false)).card = 2 ^ R.card := by
  have hset : Finset.univ.filter (fun z : Fin d → Bool => ∀ q, q ∉ R → z q = false)
      = Fintype.piFinset (fun q => if q ∈ R then (Finset.univ : Finset Bool) else {false}) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro hz q
      by_cases hq : q ∈ R
      · rw [if_pos hq]
        exact Finset.mem_univ _
      · rw [if_neg hq, hz q hq]
        exact Finset.mem_singleton_self _
    · intro hz q hq
      have := hz q
      rw [if_neg hq] at this
      exact Finset.mem_singleton.mp this
  rw [hset, Fintype.card_piFinset]
  have : ∀ q, (if q ∈ R then (Finset.univ : Finset Bool) else {false}).card
      = if q ∈ R then 2 else 1 := by
    intro q
    split_ifs <;> rfl
  simp only [this]
  rw [Finset.prod_ite_mem Finset.univ R (fun _ => 2)]
  simp
theorem ceil_le {C N M : ℕ} (hC : 0 < C) (hNM : N ≤ C * M) : (N + C - 1) / C ≤ M := by
  have h1 : (N + C - 1) / C < M + 1 := by
    rw [Nat.div_lt_iff_lt_mul hC]
    have : (M + 1) * C = C * M + C := by ring
    rw [this]
    generalize C * M = X at *
    omega
  omega
theorem count {d : ℕ} {ι : Type} [DecidableEq ι] (A B : Finset (Fin d)) (hAB : A.card = B.card)
    (P Q : Finset ι) (γ : ι → Fin d → Bool)
    (h1 : ∀ i ∈ P, ∀ j ∈ P, i ≠ j → ∃ q, q ∉ A ∧ γ i q ≠ γ j q)
    (h2 : ∀ i ∈ Q, ∀ j ∈ Q, i ≠ j → ∃ q, q ∉ B ∧ γ i q ≠ γ j q)
    (h3 : ∀ i ∈ P, ∀ j ∈ Q, ∃ q, q ∉ A ∧ q ∉ B ∧ γ i q ≠ γ j q) :
    (P.card + 2^(A \ B).card - 1) / 2^(A \ B).card
      + (Q.card + 2^(A \ B).card - 1) / 2^(A \ B).card ≤ 2^(d - (A ∪ B).card) := by
  have hBA : (B \ A).card = (A \ B).card := by
    have e1 := Finset.card_sdiff_add_card_inter A B
    have e2 := Finset.card_sdiff_add_card_inter B A
    rw [Finset.inter_comm] at e2
    omega
  have hcpos : 0 < 2^(A \ B).card := by positivity
  let κ : ι → Fin d → Bool := fun i q => if q ∈ A ∪ B then false else γ i q
  have hdisj : Disjoint (P.image κ) (Q.image κ) := by
    rw [Finset.disjoint_left]
    intro v hvP hvQ
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hvP
    obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp hvQ
    obtain ⟨q, hqA, hqB, hq⟩ := h3 i hi j hj
    have := congrFun hji q
    have hq' : q ∉ A ∪ B := by simp [hqA, hqB]
    simp only [κ, if_neg hq'] at this
    exact hq this.symm
  have hsub : P.image κ ∪ Q.image κ ⊆
      Finset.univ.filter (fun z : Fin d → Bool => ∀ q, q ∉ (A ∪ B)ᶜ → z q = false) := by
    intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro q hq
    rw [Finset.mem_compl, not_not] at hq
    rcases Finset.mem_union.mp hv with hv | hv
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
      simp only [κ, if_pos hq]
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
      simp only [κ, if_pos hq]
  have hK : (P.image κ).card + (Q.image κ).card ≤ 2^(d - (A ∪ B).card) := by
    rw [← Finset.card_union_of_disjoint hdisj]
    calc (P.image κ ∪ Q.image κ).card ≤ _ := Finset.card_le_card hsub
      _ = 2 ^ ((A ∪ B)ᶜ).card := card_mask _
      _ = 2 ^ (d - (A ∪ B).card) := by rw [Finset.card_compl, Fintype.card_fin]
  have hP : P.card ≤ 2^(A \ B).card * (P.image κ).card := by
    apply Finset.card_le_mul_card_image
    intro v _
    let ρ : ι → Fin d → Bool := fun i q => if q ∈ B \ A then γ i q else false
    calc (P.filter (fun i => κ i = v)).card
        ≤ (Finset.univ.filter (fun z : Fin d → Bool => ∀ q, q ∉ B \ A → z q = false)).card := by
          apply Finset.card_le_card_of_injOn ρ
          · intro i _
            rw [Finset.mem_coe, Finset.mem_filter]
            refine ⟨Finset.mem_univ _, fun q hq => ?_⟩
            simp only [ρ, if_neg hq]
          · intro i hi j hj hij
            by_contra hne
            rw [Finset.mem_coe, Finset.mem_filter] at hi hj
            obtain ⟨q, hqA, hq⟩ := h1 i hi.1 j hj.1 hne
            by_cases hqB : q ∈ B
            · have hq' : q ∈ B \ A := Finset.mem_sdiff.mpr ⟨hqB, hqA⟩
              have := congrFun hij q
              simp only [ρ, if_pos hq'] at this
              exact hq this
            · have hq' : q ∉ A ∪ B := by simp [hqA, hqB]
              have := congrFun (hi.2.trans hj.2.symm) q
              simp only [κ, if_neg hq'] at this
              exact hq this
      _ = 2 ^ (B \ A).card := card_mask _
      _ = 2 ^ (A \ B).card := by rw [hBA]
  have hQ : Q.card ≤ 2^(A \ B).card * (Q.image κ).card := by
    apply Finset.card_le_mul_card_image
    intro v _
    let ρ : ι → Fin d → Bool := fun i q => if q ∈ A \ B then γ i q else false
    calc (Q.filter (fun i => κ i = v)).card
        ≤ (Finset.univ.filter (fun z : Fin d → Bool => ∀ q, q ∉ A \ B → z q = false)).card := by
          apply Finset.card_le_card_of_injOn ρ
          · intro i _
            rw [Finset.mem_coe, Finset.mem_filter]
            refine ⟨Finset.mem_univ _, fun q hq => ?_⟩
            simp only [ρ, if_neg hq]
          · intro i hi j hj hij
            by_contra hne
            rw [Finset.mem_coe, Finset.mem_filter] at hi hj
            obtain ⟨q, hqB, hq⟩ := h2 i hi.1 j hj.1 hne
            by_cases hqA : q ∈ A
            · have hq' : q ∈ A \ B := Finset.mem_sdiff.mpr ⟨hqA, hqB⟩
              have := congrFun hij q
              simp only [ρ, if_pos hq'] at this
              exact hq this
            · have hq' : q ∉ A ∪ B := by simp [hqA, hqB]
              have := congrFun (hi.2.trans hj.2.symm) q
              simp only [κ, if_neg hq'] at this
              exact hq this
      _ = 2 ^ (A \ B).card := card_mask _
  have e1 := ceil_le hcpos hP
  have e2 := ceil_le hcpos hQ
  omega
theorem exists_inj_into {α β : Type} [Fintype α] [DecidableEq β] (t : Finset β)
    (h : Fintype.card α ≤ t.card) :
    ∃ f : α → β, Function.Injective f ∧ ∀ x, f x ∈ t := by
  have h2 : Fintype.card α ≤ Fintype.card t := by
    rw [Fintype.card_coe]
    exact h
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le h2
  exact ⟨fun x => (e x).1, fun x y hxy => e.injective (Subtype.ext hxy), fun x => (e x).2⟩
theorem exists_injOn_into {α β : Type} [DecidableEq α] [DecidableEq β] [Inhabited β]
    (s : Finset α) (t : Finset β) (h : s.card ≤ t.card) :
    ∃ f : α → β, (∀ x ∈ s, ∀ y ∈ s, f x = f y → x = y) ∧ ∀ x ∈ s, f x ∈ t := by
  have h2 : Fintype.card s ≤ t.card := by
    rw [Fintype.card_coe]
    exact h
  obtain ⟨g, hg, hgt⟩ := exists_inj_into t h2
  refine ⟨fun x => if hx : x ∈ s then g ⟨x, hx⟩ else default, ?_, ?_⟩
  · intro x hx y hy hxy
    simp only [dif_pos hx, dif_pos hy] at hxy
    exact congrArg Subtype.val (hg hxy)
  · intro x hx
    simp only [dif_pos hx]
    exact hgt _
theorem construct {a h l d k : ℕ} (charge : Fin (a+3) → Bool)
    (hch : (Finset.univ.filter (fun i => charge i = true)).card % 2 = 1)
    (slot : Fin (a+3) → Fin h ↪ Fin d) {H : Type} [Fintype H] [DecidableEq H]
    (hint : Fin (a+3) → H)
    (hcardH : Fintype.card H * 2^(h*l) ≤ 2^k)
    (code : Fin (a+3) → Fin d → Bool)
    (hcode0 : ∀ i b, code i (slot i b) = false)
    (hsep : ∀ i j, i ≠ j → hint i = hint j →
      ∃ q, (∀ b, slot i b ≠ q) ∧ (∀ b, slot j b ≠ q) ∧ code i q ≠ code j q) :
    ∃ (first : Fin d → (Fin (a+3) → Bool) → (Fin (a+3) → Fin h → Bool) → Bool)
      (last : (Fin d → Bool) → (Fin (a+3) → Bool) →
        ((Fin h → Bool) × (Fin (a+3) → Fin h → Fin l → Bool)) → Fin k → Bool)
      (out : (Fin d → Bool) → (Fin k → Bool) →
        Fin (a+3) × (Fin h → Bool) × (Fin h → Fin l → Bool)),
      Valid charge slot first last out := by
  classical
  choose sel hsel using exists_viol charge hch
  have hc : Fintype.card (H × (Fin h → Fin l → Bool)) ≤ Fintype.card (Fin k → Bool) := by
    rw [Fintype.card_prod, card_T]
    simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    exact hcardH
  obtain ⟨enc⟩ := Function.Embedding.nonempty_of_card_le hc
  have : Nonempty (H × (Fin h → Fin l → Bool)) := ⟨(hint 0, fun _ _ => false)⟩
  obtain ⟨dec, hdec⟩ : ∃ dec : (Fin k → Bool) → H × (Fin h → Fin l → Bool),
      ∀ y, dec (enc y) = y := ⟨Function.invFun enc, Function.leftInverse_invFun enc.injective⟩
  obtain ⟨first, hfirst⟩ : ∃ f : Fin d → (Fin (a+3) → Bool) → (Fin (a+3) → Fin h → Bool) → Bool,
      f = fun p x tbl => decide (∃ b, tbl (sel x) b = true) || code (sel x) p := ⟨_, rfl⟩
  have hz_slot : ∀ x (u : (Fin h → Bool) × (Fin (a+3) → Fin h → Fin l → Bool)) b, Phi slot first x (visF u) (slot (sel x) b) = visF u (sel x) b := by
    intro x u b
    rw [hfirst]
    simp only [Phi]
    rw [hcode0, Bool.or_false]
    have key : (∃ b', (decide (slot (sel x) b' = slot (sel x) b) && visF u (sel x) b') = true)
        ↔ visF u (sel x) b = true := by
      constructor
      · rintro ⟨b', hb'⟩
        rw [Bool.and_eq_true, decide_eq_true_iff] at hb'
        rw [← (slot (sel x)).injective hb'.1]
        exact hb'.2
      · intro hb
        exact ⟨b, by simp [hb]⟩
    rw [Bool.eq_iff_iff, decide_eq_true_iff]
    exact key
  have hz_out : ∀ x (u : (Fin h → Bool) × (Fin (a+3) → Fin h → Fin l → Bool)) q, (∀ b, slot (sel x) b ≠ q) →
      Phi slot first x (visF u) q = code (sel x) q := by
    intro x u q hq
    rw [hfirst]
    simp only [Phi]
    simp [hq]
  obtain ⟨edge, hedge⟩ : ∃ edge : (Fin d → Bool) → H → Fin (a+3), ∀ z hh i, hint i = hh →
      (∀ q, (∀ b, slot i b ≠ q) → z q = code i q) → edge z hh = i := by
    refine ⟨fun z hh => if hex : ∃ i, hint i = hh ∧ ∀ q, (∀ b, slot i b ≠ q) → z q = code i q
      then Classical.choose hex else 0, ?_⟩
    intro z hh i hi hz
    have hex : ∃ i, hint i = hh ∧ ∀ q, (∀ b, slot i b ≠ q) → z q = code i q := ⟨i, hi, hz⟩
    simp only [dif_pos hex]
    have hspec := Classical.choose_spec hex
    by_contra hne
    obtain ⟨q, hq1, hq2, hq3⟩ := hsep _ _ hne (hspec.1.trans hi.symm)
    exact hq3 ((hspec.2 q hq1).symm.trans (hz q hq2))
  refine ⟨first, fun z x u => enc (hint (sel x), u.2 (sel x)),
    fun z msg => (edge z (dec msg).1, fun b => z (slot (edge z (dec msg).1) b), (dec msg).2), ?_⟩
  intro x u
  dsimp only
  rw [hdec]
  dsimp only
  rw [hedge (Phi slot first x (visF u)) (hint (sel x)) (sel x) rfl (hz_out x u)]
  exact ⟨hsel x, funext (hz_slot x u), rfl⟩
theorem mem_slot {a h d : ℕ} (A B : Finset (Fin d)) (tag : Fin (a+3) → Bool)
    (slot : Fin (a+3) → Fin h ↪ Fin d)
    (hslot : ∀ i, Finset.univ.image (slot i) = (if tag i then A else B))
    (i : Fin (a+3)) (b : Fin h) :
    slot i b ∈ (if tag i then A else B) := by
  rw [← hslot i]
  exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
theorem codes_B {a h d : ℕ} (A B : Finset (Fin d)) (tag : Fin (a+3) → Bool)
    (slot : Fin (a+3) → Fin h ↪ Fin d)
    (hA : A.card = h) (hB : B.card = h) (hm : a + 3 ≤ 2^(d-h))
    (hslot : ∀ i, Finset.univ.image (slot i) = (if tag i then A else B)) :
    ∃ code : Fin (a+3) → Fin d → Bool, (∀ i b, code i (slot i b) = false) ∧
      (∀ i j, i ≠ j → tag i = tag j →
        ∃ q, (∀ b, slot i b ≠ q) ∧ (∀ b, slot j b ≠ q) ∧ code i q ≠ code j q) := by
  have hmA : Fintype.card (Fin (a+3)) ≤
      (Finset.univ.filter (fun z : Fin d → Bool => ∀ q, q ∉ Aᶜ → z q = false)).card := by
    rw [card_mask, Finset.card_compl, Fintype.card_fin, Fintype.card_fin, hA]
    exact hm
  have hmB : Fintype.card (Fin (a+3)) ≤
      (Finset.univ.filter (fun z : Fin d → Bool => ∀ q, q ∉ Bᶜ → z q = false)).card := by
    rw [card_mask, Finset.card_compl, Fintype.card_fin, Fintype.card_fin, hB]
    exact hm
  obtain ⟨fA, hfAinj, hfAmem⟩ := exists_inj_into _ hmA
  obtain ⟨fB, hfBinj, hfBmem⟩ := exists_inj_into _ hmB
  have hA0 : ∀ i q, q ∈ A → fA i q = false := by
    intro i q hq
    exact (Finset.mem_filter.mp (hfAmem i)).2 q (by rw [Finset.mem_compl, not_not]; exact hq)
  have hB0 : ∀ i q, q ∈ B → fB i q = false := by
    intro i q hq
    exact (Finset.mem_filter.mp (hfBmem i)).2 q (by rw [Finset.mem_compl, not_not]; exact hq)
  refine ⟨fun i => if tag i then fA i else fB i, ?_, ?_⟩
  · intro i b
    have hmem := mem_slot A B tag slot hslot i b
    by_cases ht : tag i = true
    · rw [if_pos ht] at hmem
      simp only [if_pos ht]
      exact hA0 i _ hmem
    · rw [if_neg ht] at hmem
      simp only [if_neg ht]
      exact hB0 i _ hmem
  · intro i j hij htag
    by_cases ht : tag i = true
    · have ht' : tag j = true := by rw [← htag]; exact ht
      have hne : fA i ≠ fA j := fun hh => hij (hfAinj hh)
      obtain ⟨q, hq⟩ := Function.ne_iff.mp hne
      have hqA : q ∉ A := fun hqA => hq ((hA0 i q hqA).trans (hA0 j q hqA).symm)
      refine ⟨q, fun b hb => hqA ?_, fun b hb => hqA ?_, ?_⟩
      · have := mem_slot A B tag slot hslot i b
        rw [if_pos ht, hb] at this
        exact this
      · have := mem_slot A B tag slot hslot j b
        rw [if_pos ht', hb] at this
        exact this
      · simp only [if_pos ht, if_pos ht']
        exact hq
    · have ht' : ¬ tag j = true := by rw [← htag]; exact ht
      have hne : fB i ≠ fB j := fun hh => hij (hfBinj hh)
      obtain ⟨q, hq⟩ := Function.ne_iff.mp hne
      have hqB : q ∉ B := fun hqB => hq ((hB0 i q hqB).trans (hB0 j q hqB).symm)
      refine ⟨q, fun b hb => hqB ?_, fun b hb => hqB ?_, ?_⟩
      · have := mem_slot A B tag slot hslot i b
        rw [if_neg ht, hb] at this
        exact this
      · have := mem_slot A B tag slot hslot j b
        rw [if_neg ht', hb] at this
        exact this
      · simp only [if_neg ht, if_neg ht']
        exact hq
theorem le_mul_ceil {C N : ℕ} (hC : 0 < C) : N ≤ (N + C - 1) / C * C := by
  have h1 := Nat.div_add_mod (N + C - 1) C
  have h2 := Nat.mod_lt (N + C - 1) hC
  rw [mul_comm]
  generalize C * ((N + C - 1) / C) = X at *
  generalize (N + C - 1) % C = r at *
  omega
theorem codes_A {a h d : ℕ} (A B : Finset (Fin d)) (tag : Fin (a+3) → Bool)
    (slot : Fin (a+3) → Fin h ↪ Fin d)
    (hA : A.card = h) (hB : B.card = h)
    (hslot : ∀ i, Finset.univ.image (slot i) = (if tag i then A else B))
    (hfits : ((Finset.univ.filter (fun i => tag i = true)).card + 2^(A \ B).card - 1)
        / 2^(A \ B).card
      + (a + 3 - (Finset.univ.filter (fun i => tag i = true)).card + 2^(A \ B).card - 1)
        / 2^(A \ B).card ≤ 2^(d - (A ∪ B).card)) :
    ∃ code : Fin (a+3) → Fin d → Bool, (∀ i b, code i (slot i b) = false) ∧
      (∀ i j, i ≠ j → ∃ q, (∀ b, slot i b ≠ q) ∧ (∀ b, slot j b ≠ q) ∧ code i q ≠ code j q) := by
  classical
  have hBA : (B \ A).card = (A \ B).card := by
    have e1 := Finset.card_sdiff_add_card_inter A B
    have e2 := Finset.card_sdiff_add_card_inter B A
    rw [Finset.inter_comm] at e2
    omega
  have hcpos : 0 < 2^(A \ B).card := by positivity
  have hPQ : (Finset.univ.filter (fun i : Fin (a+3) => tag i = true)).card
      + (Finset.univ.filter (fun i : Fin (a+3) => ¬ tag i = true)).card = a + 3 := by
    rw [Finset.card_filter_add_card_filter_not, Finset.card_univ, Fintype.card_fin]
  set P := Finset.univ.filter (fun i : Fin (a+3) => tag i = true) with hPdef
  set Q := Finset.univ.filter (fun i : Fin (a+3) => ¬ tag i = true) with hQdef
  set c := 2^(A \ B).card with hc
  have hQc : a + 3 - P.card = Q.card := by omega
  rw [hQc] at hfits
  set cA := (P.card + c - 1) / c with hcA
  set cB := (Q.card + c - 1) / c with hcB
  set MK := Finset.univ.filter (fun z : Fin d → Bool => ∀ q, q ∉ (A ∪ B)ᶜ → z q = false)
    with hMKdef
  have hMK : MK.card = 2^(d - (A ∪ B).card) := by
    rw [hMKdef, card_mask, Finset.card_compl, Fintype.card_fin]
  obtain ⟨CA, hCAsub, hCAcard⟩ := Finset.exists_subset_card_eq (s := MK) (n := cA)
    (by rw [hMK]; exact le_trans (Nat.le_add_right _ _) hfits)
  obtain ⟨CB, hCBsub, hCBcard⟩ := Finset.exists_subset_card_eq (s := MK \ CA) (n := cB)
    (by
      rw [Finset.card_sdiff_of_subset hCAsub, hMK, hCAcard]
      exact Nat.le_sub_of_add_le (by rw [add_comm]; exact hfits))
  set MBA := Finset.univ.filter (fun z : Fin d → Bool => ∀ q, q ∉ B \ A → z q = false)
    with hMBAdef
  set MAB := Finset.univ.filter (fun z : Fin d → Bool => ∀ q, q ∉ A \ B → z q = false)
    with hMABdef
  have hMBA : MBA.card = c := by rw [hMBAdef, card_mask, hBA]
  have hMAB : MAB.card = c := by rw [hMABdef, card_mask]
  have hnA : P.card ≤ (CA ×ˢ MBA).card := by
    rw [Finset.card_product, hCAcard, hMBA]
    exact le_mul_ceil hcpos
  have hnB : Q.card ≤ (CB ×ˢ MAB).card := by
    rw [Finset.card_product, hCBcard, hMAB]
    exact le_mul_ceil hcpos
  obtain ⟨fA, hfAinj, hfAmem⟩ := exists_injOn_into P (CA ×ˢ MBA) hnA
  obtain ⟨fB, hfBinj, hfBmem⟩ := exists_injOn_into Q (CB ×ˢ MAB) hnB
  have memA : ∀ i, tag i = true → (fA i).1 ∈ CA ∧ (fA i).2 ∈ MBA := fun i ht =>
    Finset.mem_product.mp (hfAmem i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩))
  have memB : ∀ i, ¬ tag i = true → (fB i).1 ∈ CB ∧ (fB i).2 ∈ MAB := fun i ht =>
    Finset.mem_product.mp (hfBmem i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩))
  let f : Fin (a+3) → (Fin d → Bool) × (Fin d → Bool) := fun i => if tag i then fA i else fB i
  let R : Fin (a+3) → Finset (Fin d) := fun i => if tag i then B \ A else A \ B
  let S : Fin (a+3) → Finset (Fin d) := fun i => if tag i then A else B
  have F1 : ∀ i q, q ∈ A ∪ B → (f i).1 q = false := by
    intro i q hq
    have hq' : q ∉ (A ∪ B)ᶜ := by
      rw [Finset.mem_compl, not_not]
      exact hq
    by_cases ht : tag i = true
    · simp only [f, if_pos ht]
      exact (Finset.mem_filter.mp (hCAsub (memA i ht).1)).2 q hq'
    · simp only [f, if_neg ht]
      exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp (hCBsub (memB i ht).1)).1).2 q hq'
  have F2 : ∀ i q, q ∉ R i → (f i).2 q = false := by
    intro i q hq
    by_cases ht : tag i = true
    · simp only [R, if_pos ht] at hq
      simp only [f, if_pos ht]
      exact (Finset.mem_filter.mp (memA i ht).2).2 q hq
    · simp only [R, if_neg ht] at hq
      simp only [f, if_neg ht]
      exact (Finset.mem_filter.mp (memB i ht).2).2 q hq
  have hRsub : ∀ i q, q ∈ R i → q ∈ A ∪ B := by
    intro i q hq
    by_cases ht : tag i = true
    · simp only [R, if_pos ht] at hq
      exact Finset.mem_union_right _ (Finset.mem_sdiff.mp hq).1
    · simp only [R, if_neg ht] at hq
      exact Finset.mem_union_left _ (Finset.mem_sdiff.mp hq).1
  have hRS : ∀ i q, q ∈ R i → q ∉ S i := by
    intro i q hq
    by_cases ht : tag i = true
    · simp only [R, if_pos ht] at hq
      simp only [S, if_pos ht]
      exact (Finset.mem_sdiff.mp hq).2
    · simp only [R, if_neg ht] at hq
      simp only [S, if_neg ht]
      exact (Finset.mem_sdiff.mp hq).2
  have hSsub : ∀ i q, q ∈ S i → q ∈ A ∪ B := by
    intro i q hq
    by_cases ht : tag i = true
    · simp only [S, if_pos ht] at hq
      exact Finset.mem_union_left _ hq
    · simp only [S, if_neg ht] at hq
      exact Finset.mem_union_right _ hq
  have hslotS : ∀ i b, slot i b ∈ S i := fun i b => mem_slot A B tag slot hslot i b
  have Hsame : ∀ i j, i ≠ j → tag i = tag j → f i ≠ f j := by
    intro i j hij htag hf
    by_cases ht : tag i = true
    · have ht' : tag j = true := by rw [← htag]; exact ht
      simp only [f, if_pos ht, if_pos ht'] at hf
      exact hij (hfAinj i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩) j
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht'⟩) hf)
    · have ht' : ¬ tag j = true := by rw [← htag]; exact ht
      simp only [f, if_neg ht, if_neg ht'] at hf
      exact hij (hfBinj i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩) j
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht'⟩) hf)
  have Hdiff : ∀ i j, tag i ≠ tag j → (f i).1 ≠ (f j).1 := by
    intro i j htag hf
    by_cases ht : tag i = true
    · have ht' : ¬ tag j = true := by
        intro hh
        exact htag (ht.trans hh.symm)
      simp only [f, if_pos ht, if_neg ht'] at hf
      have h1 := (memA i ht).1
      have h2 := (Finset.mem_sdiff.mp (hCBsub (memB j ht').1)).2
      rw [hf] at h1
      exact h2 h1
    · have ht' : tag j = true := by
        cases hj : tag j
        · exfalso
          apply htag
          rw [hj]
          simpa using ht
        · rfl
      simp only [f, if_neg ht, if_pos ht'] at hf
      have h1 := (memA j ht').1
      have h2 := (Finset.mem_sdiff.mp (hCBsub (memB i ht).1)).2
      rw [← hf] at h1
      exact h2 h1
  have hRS_eq : ∀ i j, tag i = tag j → R i = R j ∧ S i = S j := by
    intro i j htag
    exact ⟨by simp only [R, htag], by simp only [S, htag]⟩
  refine ⟨fun i q => (f i).1 q || (f i).2 q, ?_, ?_⟩
  · intro i b
    have h1 := F1 i _ (hSsub i _ (hslotS i b))
    have h2 := F2 i _ (fun hh => hRS i _ hh (hslotS i b))
    simp only [h1, h2, Bool.or_false]
  · intro i j hij
    have key : (f i).1 ≠ (f j).1 ∨ (tag i = tag j ∧ (f i).2 ≠ (f j).2) := by
      by_cases htag : tag i = tag j
      · have := Hsame i j hij htag
        by_cases h1 : (f i).1 = (f j).1
        · right
          exact ⟨htag, fun h2 => this (Prod.ext h1 h2)⟩
        · left
          exact h1
      · left
        exact Hdiff i j htag
    rcases key with h1 | ⟨htag, h2⟩
    · obtain ⟨q, hq⟩ := Function.ne_iff.mp h1
      have hqAB : q ∉ A ∪ B := fun hh => hq ((F1 i q hh).trans (F1 j q hh).symm)
      refine ⟨q, fun b hb => hqAB ?_, fun b hb => hqAB ?_, ?_⟩
      · rw [← hb]
        exact hSsub i _ (hslotS i b)
      · rw [← hb]
        exact hSsub j _ (hslotS j b)
      · have e1 := F2 i q (fun hh => hqAB (hRsub i q hh))
        have e2 := F2 j q (fun hh => hqAB (hRsub j q hh))
        simp only [e1, e2, Bool.or_false]
        exact hq
    · obtain ⟨q, hq⟩ := Function.ne_iff.mp h2
      obtain ⟨hR, hS⟩ := hRS_eq i j htag
      have hqR : q ∈ R i := by
        by_contra hh
        have hh' : q ∉ R j := by rw [← hR]; exact hh
        exact hq ((F2 i q hh).trans (F2 j q hh').symm)
      have hqAB := hRsub i q hqR
      have hqS := hRS i q hqR
      refine ⟨q, fun b hb => hqS ?_, fun b hb => hqS ?_, ?_⟩
      · rw [← hb]
        exact hslotS i b
      · rw [hS, ← hb]
        exact hslotS j b
      · have e1 := F1 i q hqAB
        have e2 := F1 j q hqAB
        simp only [e1, e2, Bool.false_or]
        exact hq
theorem main (a h l d : ℕ) (hl : 0 < l) (charge : Fin (a+3) → Bool)
    (hch : (Finset.univ.filter (fun i => charge i = true)).card % 2 = 1)
    (A B : Finset (Fin d)) (tag : Fin (a+3) → Bool) (slot : Fin (a+3) → Fin h ↪ Fin d)
    (hA : A.card = h) (hB : B.card = h) (hm : a + 3 ≤ 2^(d-h))
    (hslot : ∀ i, Finset.univ.image (slot i) = (if tag i then A else B)) (k : ℕ) :
    (∃ (first : Fin d → (Fin (a+3) → Bool) → (Fin (a+3) → Fin h → Bool) → Bool)
      (last : (Fin d → Bool) → (Fin (a+3) → Bool) →
        ((Fin h → Bool) × (Fin (a+3) → Fin h → Fin l → Bool)) → Fin k → Bool)
      (out : (Fin d → Bool) → (Fin k → Bool) →
        Fin (a+3) × (Fin h → Bool) × (Fin h → Fin l → Bool)),
      Valid charge slot first last out) ↔
    h * l + (if ((Finset.univ.filter (fun i => tag i = true)).card + 2^(A \ B).card - 1)
        / 2^(A \ B).card
      + (a + 3 - (Finset.univ.filter (fun i => tag i = true)).card + 2^(A \ B).card - 1)
        / 2^(A \ B).card ≤ 2^(d - (A ∪ B).card) then 0 else 1) ≤ k := by
  constructor
  · rintro ⟨first, last, out, hv⟩
    have h1 := lower_hl hl hch hv
    split_ifs with hfits
    · omega
    · by_contra hk
      have hk' : k = h * l := by omega
      apply hfits
      choose xs hxs using uniq_viol charge hch
      have HC : ∀ i j V V', Phi slot first (xs i) V = Phi slot first (xs j) V' →
          i = j ∧ V i = V' j :=
        fun i j V V' hz => cond_C hl hv hk' (xs i) (xs j) i j (hxs i) (hxs j) V V' hz
      have HD := cond_D slot first xs HC
      have hnot : ∀ i q, (∀ b, slot i b ≠ q) → q ∉ (if tag i then A else B) := by
        intro i q hq hmem
        rw [← hslot i, Finset.mem_image] at hmem
        obtain ⟨b, _, hb⟩ := hmem
        exact hq b hb
      have hPQ : (Finset.univ.filter (fun i : Fin (a+3) => tag i = true)).card
          + (Finset.univ.filter (fun i : Fin (a+3) => ¬ tag i = true)).card = a + 3 := by
        rw [Finset.card_filter_add_card_filter_not, Finset.card_univ, Fintype.card_fin]
      have hQc : a + 3 - (Finset.univ.filter (fun i : Fin (a+3) => tag i = true)).card
          = (Finset.univ.filter (fun i : Fin (a+3) => ¬ tag i = true)).card := by omega
      rw [hQc]
      apply count A B (hA.trans hB.symm) _ _ (fun i => Phi slot first (xs i) (fun _ _ => false))
      · intro i hi j hj hij
        obtain ⟨q, hq1, _, hq3⟩ := HD i j hij
        have ht := (Finset.mem_filter.mp hi).2
        refine ⟨q, ?_, hq3⟩
        have := hnot i q hq1
        rw [if_pos ht] at this
        exact this
      · intro i hi j hj hij
        obtain ⟨q, hq1, _, hq3⟩ := HD i j hij
        have ht := (Finset.mem_filter.mp hi).2
        refine ⟨q, ?_, hq3⟩
        have := hnot i q hq1
        rw [if_neg ht] at this
        exact this
      · intro i hi j hj
        have hti := (Finset.mem_filter.mp hi).2
        have htj := (Finset.mem_filter.mp hj).2
        have hij : i ≠ j := by
          intro hh
          rw [hh] at hti
          exact htj hti
        obtain ⟨q, hq1, hq2, hq3⟩ := HD i j hij
        refine ⟨q, ?_, ?_, hq3⟩
        · have := hnot i q hq1
          rw [if_pos hti] at this
          exact this
        · have := hnot j q hq2
          rw [if_neg htj] at this
          exact this
  · intro hk
    split_ifs at hk with hfits
    · obtain ⟨code, hcode0, hsep⟩ := codes_A A B tag slot hA hB hslot hfits
      refine construct charge hch slot (H := Unit) (fun _ => ()) ?_ code hcode0
        (fun i j hij _ => hsep i j hij)
      rw [Fintype.card_unit, one_mul]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    · obtain ⟨code, hcode0, hsep⟩ := codes_B A B tag slot hA hB hm hslot
      refine construct charge hch slot tag ?_ code hcode0 hsep
      rw [Fintype.card_bool, ← pow_succ']
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
end PEqualNP.Outside.L_pcx_439
theorem PEqualNP.Outside.L_pcx_439 : ∀ a h l d : ℕ, 0 < l →
  let m := a+3
  let I := Fin m
  let J := Fin h
  let Z := Fin d → Bool
  let W := J → Bool
  let T := J → Fin l → Bool
  let X := I → Bool
  let U := W × (I → T)
  let vis := fun (u : U) (i : I) (b : J) =>
    xor (u.1 b) (decide ((Finset.univ.filter (fun p => u.2 i b p = true)).card % 2 = 1))
  ∀ (charge : X), (Finset.univ.filter (fun i => charge i = true)).card % 2 = 1 →
    ∀ (A B : Finset (Fin d)) (tag : I → Bool) (slot : I → J ↪ Fin d),
      A.card = h → B.card = h → m ≤ 2^(d-h) →
      (∀ i, Finset.univ.image (slot i) = (if tag i then A else B)) →
      let n := (Finset.univ.filter (fun i => tag i = true)).card
      let c := 2^(A \ B).card
      let fits := (n+c-1)/c + (m-n+c-1)/c ≤ 2^(d-(A ∪ B).card)
      ∀ k : ℕ,
        (∃ (first : Fin d → X → (I → W) → Bool)
            (last : Z → X → U → Fin k → Bool) (out : Z → (Fin k → Bool) → I × W × T),
          ∀ x u,
            let z : Z := fun p => first p x (fun i b => decide (slot i b = p) && vis u i b)
            let ans := out z (last z x u)
            xor (x ans.1) (x (ans.1+1)) ≠ charge ans.1 ∧
              ans.2.1 = vis u ans.1 ∧ ans.2.2 = u.2 ans.1) ↔
          h*l + (if fits then 0 else 1) ≤ k := by
  intro a h l d hl m I J Z W T X U vis charge hch A B tag slot hA hB hm hslot n c fits k
  exact PEqualNP.Outside.L_pcx_439.main a h l d hl charge hch A B tag slot hA hB hm hslot k
