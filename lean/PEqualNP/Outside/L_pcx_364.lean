import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_pcx_364
abbrev Ed (k : ℕ) := {p : Fin k × Fin k // p.1 < p.2}
abbrev wd (k : ℕ) : ℕ := 1 + Nat.log 2 (k+1)
abbrev CG (k : ℕ) := Fin k × (Fin (wd k) × Fin 4)
abbrev Gate (k : ℕ) := Ed k ⊕ CG k
abbrev W0 (k : ℕ) := Unit ⊕ (Fin k ⊕ Gate k)
abbrev Wire (k : ℕ) := Bool × W0 k
abbrev Ed0 (k : ℕ) := (Gate k × Fin 9) ⊕ W0 k
abbrev Dart (k : ℕ) := (Bool × Ed0 k) × Bool
def fW (k : ℕ) : Wire k := (false, Sum.inl ())
def inpW (k : ℕ) (i : Fin k) : Wire k := (true, Sum.inr (Sum.inl i))
def goutW (k : ℕ) (g : Gate k) : Wire k := (true, Sum.inr (Sum.inr g))
def cntW (k : ℕ) (t : Fin k) (j : Fin (wd k)) (q : Fin 4) : Wire k := goutW k (Sum.inr (t, j, q))
def negW (k : ℕ) (x : Wire k) : Wire k := (!x.1, x.2)
def flipW (k : ℕ) (m : Bool) (x : Wire k) : Wire k := (xor m x.1, x.2)
def regW (k : ℕ) (t : ℕ) (j : Fin (wd k)) : Wire k :=
  if h : 0 < t ∧ t - 1 < k then cntW k ⟨t - 1, h.2⟩ j 3 else fW k
def carW (k : ℕ) (t : Fin k) (j : Fin (wd k)) : Wire k :=
  if 0 < j.val then negW k (cntW k t ⟨j.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) j.isLt⟩ 0)
  else inpW k t
def gIn (k : ℕ) : Gate k → Wire k × Wire k
  | Sum.inl e => (inpW k e.1.1, inpW k e.1.2)
  | Sum.inr (t, j, q) =>
    if q.val = 0 then (regW k t.val j, carW k t j)
    else if q.val = 1 then (regW k t.val j, cntW k t j 0)
    else if q.val = 2 then (carW k t j, cntW k t j 0)
    else (cntW k t j 1, cntW k t j 2)
def gadE (k : ℕ) (a b c f : Wire k) (i : Fin 9) : Wire k × Wire k :=
  ![(a, b), (a, c), (a, c), (b, c), (b, c), (a, f), (b, f), (c, f), (c, f)] i
def ends0 (k : ℕ) : Ed0 k → Wire k × Wire k
  | Sum.inl (g, i) => gadE k (gIn k g).1 (gIn k g).2 (goutW k g) (fW k) i
  | Sum.inr u => ((true, u), (false, u))
def fD (k : ℕ) (d : Dart k) : Wire k :=
  flipW k d.1.1 (if d.2 then (ends0 k d.1.2).2 else (ends0 k d.1.2).1)
def alphaD (k : ℕ) : Equiv.Perm (Dart k) where
  toFun d := (d.1, !d.2)
  invFun d := (d.1, !d.2)
  left_inv d := by simp
  right_inv d := by simp
def dartOf (k : ℕ) (x : Wire k) : Dart k := ((false, Sum.inr x.2), !x.1)
def Tv (k : ℕ) : ℕ := 4 * (6 * Fintype.card (Gate k) + Fintype.card (W0 k))
def portW (k : ℕ) : Fin k ⊕ (Ed k ⊕ (Bool × Fin (wd k))) → Wire k
  | Sum.inl i => inpW k i
  | Sum.inr (Sum.inl e) => negW k (goutW k (Sum.inl e))
  | Sum.inr (Sum.inr (b, j)) => flipW k b (regW k k j)
def GoodZ (k : ℕ) (z : Wire k → Bool) : Prop :=
  (∀ u : W0 k, z (false, u) = !z (true, u)) ∧
    ∀ g : Gate k, z (goutW k g) = !(z (gIn k g).1 && z (gIn k g).2)
def cntA (k : ℕ) (A : Finset (Fin k)) (t : ℕ) : ℕ := (A.filter (fun i => i.val < t)).card
def carA (k : ℕ) (A : Finset (Fin k)) (t : Fin k) (j : ℕ) : Bool :=
  decide (t ∈ A) && decide (∀ i, i < j → (cntA k A t.val).testBit i = true)
def valA (k : ℕ) (A : Finset (Fin k)) : W0 k → Bool
  | Sum.inl _ => true
  | Sum.inr (Sum.inl i) => decide (i ∈ A)
  | Sum.inr (Sum.inr (Sum.inl e)) => !(decide (e.1.1 ∈ A) && decide (e.1.2 ∈ A))
  | Sum.inr (Sum.inr (Sum.inr (t, j, q))) =>
    let a := (cntA k A t.val).testBit j.val
    let b := carA k A t j.val
    let n1 := !(a && b)
    let n2 := !(a && n1)
    let n3 := !(b && n1)
    if q.val = 0 then n1 else if q.val = 1 then n2 else if q.val = 2 then n3 else !(n2 && n3)
def zA (k : ℕ) (A : Finset (Fin k)) (x : Wire k) : Bool :=
  if x.1 then valA k A x.2 else !valA k A x.2
theorem pA_pow_inv {α : Type} (c : Equiv.Perm α) (G : α → Bool) (hG : ∀ x, G (c x) = G x) :
    ∀ (i : ℕ) (x : α), G ((c ^ i) x) = G x := by
  intro i
  induction i with
  | zero => intro x; rw [pow_zero, Equiv.Perm.one_apply]
  | succ m ih => intro x; rw [pow_succ', Equiv.Perm.mul_apply, hG, ih]
theorem orbit_perm {D W : Type} [Fintype D] (f : D → W) :
    ∃ π : Equiv.Perm D, (∀ d, f (π d) = f d) ∧
      ∀ g : D → Bool, (∀ d, g (π d) = g d) → ∀ d d', f d = f d' → g d = g d' := by
  classical
  choose c hc using fun w : W => Finset.exists_cycleOn (Finset.univ : Finset {d // f d = w})
  let π : Equiv.Perm D :=
    (Equiv.sigmaFiberEquiv f).symm.trans ((Equiv.sigmaCongrRight c).trans (Equiv.sigmaFiberEquiv f))
  have key : ∀ (w : W) (x : {e // f e = w}), π x.1 = (c w x).1 := by
    rintro w ⟨e, rfl⟩
    rfl
  refine ⟨π, ?_, ?_⟩
  · intro d
    have h1 : π d = (c (f d) ⟨d, rfl⟩).1 := key (f d) ⟨d, rfl⟩
    rw [h1]
    exact (c (f d) ⟨d, rfl⟩).2
  · intro g hg d d' hdd'
    have hinv : ∀ x : {e // f e = f d'}, g (c (f d') x).1 = g x.1 := by
      intro x
      rw [← key (f d') x]
      exact hg x.1
    have hx : (⟨d, hdd'⟩ : {e // f e = f d'}) ∈
        ((Finset.univ : Finset {e // f e = f d'}) : Set {e // f e = f d'}) := by simp
    have hy : (⟨d', rfl⟩ : {e // f e = f d'}) ∈
        ((Finset.univ : Finset {e // f e = f d'}) : Set {e // f e = f d'}) := by simp
    obtain ⟨i, hi⟩ := ((hc (f d')).1.2 hx hy).exists_nat_pow_eq
    have h2 := pA_pow_inv (c (f d')) (fun x => g x.1) hinv i ⟨d, hdd'⟩
    rw [hi] at h2
    exact h2.symm
theorem cost_transport {D : Type} [Fintype D] {n : ℕ} (e : D ≃ Fin n) (P : Equiv.Perm D)
    (y : Bool × Fin n → Bool) :
    (Finset.univ.filter (fun i : Fin n => y (false, i) ≠ y (true, (e.symm.trans (P.trans e)) i))).card =
    (Finset.univ.filter (fun d : D => y (false, e d) ≠ y (true, e (P d)))).card := by
  apply Finset.card_equiv e.symm
  intro i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  simp
theorem true_transport {D : Type} [Fintype D] {n : ℕ} (e : D ≃ Fin n) (y : Bool × Fin n → Bool) :
    (Finset.univ.filter (fun u : Bool × Fin n => y u = true)).card =
    (Finset.univ.filter (fun u : Bool × D => y (u.1, e u.2) = true)).card := by
  apply Finset.card_equiv ((Equiv.refl Bool).prodCongr e.symm)
  rintro ⟨b, i⟩
  simp
theorem card_le (k : ℕ) : Fintype.card (Dart k) ≤ 512 * (k+1)^2 := by
  have h1 : Fintype.card (Ed k) ≤ k * k := by
    have h := Fintype.card_subtype_le (fun p : Fin k × Fin k => p.1 < p.2)
    rw [Fintype.card_prod, Fintype.card_fin] at h
    exact h
  have h2 : wd k ≤ k + 2 := by
    have := Nat.log_le_self 2 (k+1)
    show 1 + Nat.log 2 (k+1) ≤ k + 2
    omega
  have h3 : k * wd k ≤ k * (k + 2) := Nat.mul_le_mul_left k h2
  simp only [Fintype.card_prod, Fintype.card_sum, Fintype.card_fin, Fintype.card_bool,
    Fintype.card_unit]
  nlinarith [h1, h3, Nat.zero_le (k * k), Nat.zero_le k]
def pA_mu (k : ℕ) : Equiv.Perm (Dart k) where
  toFun d := ((!d.1.1, d.1.2), d.2)
  invFun d := ((!d.1.1, d.1.2), d.2)
  left_inv d := by simp
  right_inv d := by simp
theorem pA_neg (k : ℕ) (z : Wire k → Bool) (hc : ∀ u : W0 k, z (false, u) = !z (true, u))
    (m : Bool) (x : Wire k) : z (flipW k (!m) x) = !z (flipW k m x) := by
  rcases x with ⟨c, u⟩
  cases m <;> cases c <;> simp [flipW, hc]
theorem pA_hmu (k : ℕ) (z : Wire k → Bool) (hc : ∀ u : W0 k, z (false, u) = !z (true, u))
    (d : Dart k) : z (fD k (pA_mu k d)) = !z (fD k d) :=
  pA_neg k z hc d.1.1 (if d.2 then (ends0 k d.1.2).2 else (ends0 k d.1.2).1)
theorem half_true (k : ℕ) (z : Wire k → Bool) (hc : ∀ u : W0 k, z (false, u) = !z (true, u)) :
    (Finset.univ.filter (fun u : Bool × Dart k => z (fD k u.2) = true)).card =
      Fintype.card (Dart k) := by
  have h1 : (Finset.univ.filter (fun u : Bool × Dart k => z (fD k u.2) = true)) =
      (Finset.univ : Finset Bool) ×ˢ (Finset.univ.filter (fun d : Dart k => z (fD k d) = true)) := by
    ext ⟨b, d⟩
    simp
  have h2 : (Finset.univ.filter (fun d : Dart k => z (fD k d) = true)).card =
      (Finset.univ.filter (fun d : Dart k => ¬ (z (fD k d) = true))).card := by
    apply Finset.card_equiv (pA_mu k)
    intro d
    simp [pA_hmu k z hc d]
  have h3 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Dart k)))
    (fun d : Dart k => z (fD k d) = true)
  simp only [Finset.card_univ] at h3
  rw [h1, Finset.card_product, Finset.card_univ, Fintype.card_bool]
  omega
def pB_e (p q : Bool) : ℕ := if p = q then 0 else 1
def pB_cnt (a b c f : Bool) : ℕ :=
  pB_e a b + pB_e a c + pB_e a c + pB_e b c + pB_e b c + pB_e a f + pB_e b f + pB_e c f + pB_e c f
def pB_cut (k : ℕ) (z : Wire k → Bool) (m : Bool) (e : Ed0 k) : ℕ :=
  pB_e (z (flipW k m (ends0 k e).1)) (z (flipW k m (ends0 k e).2))
def pB_G (k : ℕ) (z : Wire k → Bool) (m : Bool) (g : Gate k) : ℕ :=
  ∑ i : Fin 9, pB_cut k z m (Sum.inl (g, i))
theorem pB_e_le : ∀ p q : Bool, pB_e p q ≤ 1 := by decide
theorem pB_e_one : ∀ p q : Bool, pB_e p q = 1 ↔ q = !p := by decide
theorem pB_e_xor : ∀ m p q : Bool, pB_e (xor m p) (xor m q) = pB_e p q := by decide
theorem pB_cnt_le : ∀ a b c f : Bool, pB_cnt a b c f ≤ 6 := by decide
theorem pB_cnt_six : ∀ a b c : Bool, pB_cnt a b c false = 6 ↔ c = !(a && b) := by decide
theorem pB_cnt_xor : ∀ m a b c f : Bool,
    pB_cnt (xor m a) (xor m b) (xor m c) (xor m f) = pB_cnt a b c f := by decide
theorem pB_two : ∀ p q : Bool,
    ((if q ≠ p then 1 else 0) + (if p ≠ q then 1 else 0) : ℕ) = 2 * pB_e p q := by decide
theorem pB_gad (k : ℕ) (φ : Wire k → Bool) (a b c f : Wire k) :
    ∑ i : Fin 9, pB_e (φ (gadE k a b c f i).1) (φ (gadE k a b c f i).2) =
      pB_cnt (φ a) (φ b) (φ c) (φ f) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, gadE, Matrix.cons_val_zero,
    Matrix.cons_val_succ, pB_cnt]
  omega
theorem pB_G_eq (k : ℕ) (z : Wire k → Bool) (m : Bool) (g : Gate k) :
    pB_G k z m g = pB_cnt (z (flipW k m (gIn k g).1)) (z (flipW k m (gIn k g).2))
      (z (flipW k m (goutW k g))) (z (flipW k m (fW k))) :=
  pB_gad k (fun x => z (flipW k m x)) (gIn k g).1 (gIn k g).2 (goutW k g) (fW k)
theorem pB_W_eq (k : ℕ) (z : Wire k → Bool) (m : Bool) (u : W0 k) :
    pB_cut k z m (Sum.inr u) = pB_e (z (flipW k m (true, u))) (z (flipW k m (false, u))) := rfl
theorem pB_G_le (k : ℕ) (z : Wire k → Bool) (m : Bool) (g : Gate k) : pB_G k z m g ≤ 6 := by
  rw [pB_G_eq]
  exact pB_cnt_le _ _ _ _
theorem pB_W_le (k : ℕ) (z : Wire k → Bool) (m : Bool) (u : W0 k) :
    pB_cut k z m (Sum.inr u) ≤ 1 := by
  rw [pB_W_eq]
  exact pB_e_le _ _
theorem pB_sum_le {ι : Type} [Fintype ι] (f : ι → ℕ) (c : ℕ) (h : ∀ i, f i ≤ c) :
    ∑ i, f i ≤ Fintype.card ι * c := by
  calc ∑ i, f i ≤ ∑ _i : ι, c := Finset.sum_le_sum (fun i _ => h i)
    _ = Fintype.card ι * c := by simp
theorem pB_sum_iff {ι : Type} [Fintype ι] (f : ι → ℕ) (c : ℕ) (h : ∀ i, f i ≤ c) :
    ∑ i, f i = Fintype.card ι * c ↔ ∀ i, f i = c := by
  have := Finset.sum_eq_sum_iff_of_le (s := Finset.univ) (f := f) (g := fun _ => c)
    (fun i _ => h i)
  simpa using this
theorem pB_card (k : ℕ) (z : Wire k → Bool) :
    (Finset.univ.filter (fun d : Dart k => z (fD k d) ≠ z (fD k (alphaD k d)))).card =
      2 * ∑ m : Bool, (∑ g : Gate k, pB_G k z m g + ∑ u : W0 k, pB_cut k z m (Sum.inr u)) := by
  rw [Finset.card_filter, Fintype.sum_prod_type]
  trans ∑ x : Bool × Ed0 k, 2 * pB_cut k z x.1 x.2
  · apply Fintype.sum_congr
    intro x
    rw [Fintype.sum_bool]
    have ht : fD k (x, true) = flipW k x.1 (ends0 k x.2).2 := rfl
    have hf : fD k (x, false) = flipW k x.1 (ends0 k x.2).1 := rfl
    have hat : alphaD k (x, true) = (x, false) := rfl
    have haf : alphaD k (x, false) = (x, true) := rfl
    rw [hat, haf, ht, hf]
    exact pB_two _ _
  · rw [← Finset.mul_sum, Fintype.sum_prod_type]
    congr 1
    apply Fintype.sum_congr
    intro m
    rw [Fintype.sum_sum_type (fun e : Ed0 k => pB_cut k z (m, e).1 (m, e).2),
      Fintype.sum_prod_type]
    rfl
theorem cut_iff (k : ℕ) (z : Wire k → Bool) (hF : z (fW k) = false) :
    (Finset.univ.filter (fun d : Dart k => z (fD k d) ≠ z (fD k (alphaD k d)))).card = Tv k ↔
      GoodZ k z := by
  have hm : ∀ m : Bool, ∑ g : Gate k, pB_G k z m g + ∑ u : W0 k, pB_cut k z m (Sum.inr u) ≤
      6 * Fintype.card (Gate k) + Fintype.card (W0 k) := by
    intro m
    have h1 := pB_sum_le _ 6 (pB_G_le k z m)
    have h2 := pB_sum_le _ 1 (pB_W_le k z m)
    omega
  have e1 := pB_sum_iff _ _ hm
  rw [Fintype.card_bool] at e1
  have e2 : ∀ m : Bool, (∑ g : Gate k, pB_G k z m g + ∑ u : W0 k, pB_cut k z m (Sum.inr u) =
      6 * Fintype.card (Gate k) + Fintype.card (W0 k)) ↔
      ((∀ g, pB_G k z m g = 6) ∧ (∀ u, pB_cut k z m (Sum.inr u) = 1)) := by
    intro m
    have i1 := pB_sum_iff _ 6 (pB_G_le k z m)
    have i2 := pB_sum_iff _ 1 (pB_W_le k z m)
    have h1 := pB_sum_le _ 6 (pB_G_le k z m)
    have h2 := pB_sum_le _ 1 (pB_W_le k z m)
    constructor
    · intro h
      exact ⟨i1.1 (by omega), i2.1 (by omega)⟩
    · rintro ⟨h3, h4⟩
      have h5 := i1.2 h3
      have h6 := i2.2 h4
      omega
  have hfl : ∀ x : Wire k, flipW k false x = x := fun x => by simp [flipW]
  rw [pB_card]
  unfold Tv GoodZ
  constructor
  · intro h
    have h3 := e1.1 (by omega)
    refine ⟨fun u => ?_, fun g => ?_⟩
    · have h7 := ((e2 false).1 (h3 false)).2 u
      rw [pB_W_eq, hfl, hfl, pB_e_one] at h7
      exact h7
    · have h7 := ((e2 false).1 (h3 false)).1 g
      rw [pB_G_eq] at h7
      simp only [hfl] at h7
      rw [hF, pB_cnt_six] at h7
      exact h7
  · intro hG
    have hx : ∀ (m : Bool) (x : Wire k), z (flipW k m x) = xor m (z x) := by
      intro m x
      rcases x with ⟨p, u⟩
      have h8 := hG.1 u
      cases m <;> cases p <;> simp [flipW, h8]
    have h4 : ∀ m : Bool, (∀ g, pB_G k z m g = 6) ∧ (∀ u, pB_cut k z m (Sum.inr u) = 1) := by
      intro m
      refine ⟨fun g => ?_, fun u => ?_⟩
      · rw [pB_G_eq]
        simp only [hx]
        rw [pB_cnt_xor, hF, pB_cnt_six]
        exact hG.2 g
      · rw [pB_W_eq]
        simp only [hx]
        rw [pB_e_xor, pB_e_one]
        exact hG.1 u
    have h5 := e1.2 (fun m => (e2 m).2 (h4 m))
    omega
theorem pC_lt_pow (k : ℕ) : k < 2 ^ (wd k) := by
  have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (k+1)
  have e : wd k = (Nat.log 2 (k+1)).succ := by
    show 1 + Nat.log 2 (k+1) = Nat.log 2 (k+1) + 1
    omega
  rw [e]
  exact Nat.lt_of_succ_lt h
theorem pC_bits_eq (k a b : ℕ) (ha : a ≤ k) (hb : b ≤ k)
    (h : ∀ j : Fin (wd k), a.testBit j.val = b.testBit j.val) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < wd k
  · exact h ⟨i, hi⟩
  · have hp : 2 ^ (wd k) ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hl := pC_lt_pow k
    rw [Nat.testBit_lt_two_pow (lt_of_le_of_lt ha (lt_of_lt_of_le hl hp)),
      Nat.testBit_lt_two_pow (lt_of_le_of_lt hb (lt_of_lt_of_le hl hp))]
theorem card_eq_iff_bits (k : ℕ) (A : Finset (Fin k)) (s : ℕ) (hs : s ≤ k) :
    A.card = s ↔ ∀ j : Fin (wd k), A.card.testBit j.val = s.testBit j.val := by
  constructor
  · intro h j
    rw [h]
  · intro h
    have hA : A.card ≤ k := by
      have h1 := Finset.card_le_univ A
      rw [Fintype.card_fin] at h1
      exact h1
    exact pC_bits_eq k _ _ hA hs h
theorem pC_inc (j : ℕ) : ∀ c : ℕ,
    (c+1).testBit j = xor (c.testBit j) (decide (∀ i, i < j → c.testBit i = true)) := by
  induction j with
  | zero =>
    intro c
    have h0 : (∀ i, i < 0 → c.testBit i = true) := fun i hi => absurd hi (Nat.not_lt_zero i)
    rw [decide_eq_true h0]
    simp only [Nat.testBit_zero]
    rcases Nat.mod_two_eq_zero_or_one c with h | h
    · have h1 : (c + 1) % 2 = 1 := by omega
      simp [h, h1]
    · have h1 : (c + 1) % 2 = 0 := by omega
      simp [h, h1]
  | succ j ih =>
    intro c
    rw [Nat.testBit_add_one, Nat.testBit_add_one]
    rcases Nat.mod_two_eq_zero_or_one c with h | h
    · have h1 : (c + 1) / 2 = c / 2 := by omega
      have h2 : decide (∀ i, i < j + 1 → c.testBit i = true) = false := by
        rw [decide_eq_false_iff_not]
        intro hc
        have h3 := hc 0 (Nat.succ_pos j)
        simp [Nat.testBit_zero, h] at h3
      rw [h1, h2, Bool.xor_false]
    · have h1 : (c + 1) / 2 = c / 2 + 1 := by omega
      have h2 : decide (∀ i, i < j → (c / 2).testBit i = true) =
          decide (∀ i, i < j + 1 → c.testBit i = true) := by
        rw [decide_eq_decide]
        constructor
        · intro hc i hi
          cases i with
          | zero => simp [Nat.testBit_zero, h]
          | succ i =>
            rw [Nat.testBit_add_one]
            exact hc i (by omega)
        · intro hc i hi
          have h3 := hc (i + 1) (by omega)
          rwa [Nat.testBit_add_one] at h3
      rw [h1, ih (c / 2), h2]
theorem pC_dec_succ (c m : ℕ) :
    decide (∀ i, i < m + 1 → c.testBit i = true) =
      (decide (∀ i, i < m → c.testBit i = true) && c.testBit m) := by
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_iff, Bool.and_eq_true]
  exact Nat.forall_lt_succ_right
theorem pC_cnt_zero (k : ℕ) (A : Finset (Fin k)) : cntA k A 0 = 0 := by
  simp [cntA]
theorem pC_cnt_k (k : ℕ) (A : Finset (Fin k)) : cntA k A k = A.card := by
  simp [cntA]
theorem pC_cnt_succ (k : ℕ) (A : Finset (Fin k)) (t : Fin k) :
    cntA k A (t.val + 1) = cntA k A t.val + (if t ∈ A then 1 else 0) := by
  unfold cntA
  have e : A.filter (fun i => i.val < t.val + 1) =
      A.filter (fun i => i.val < t.val) ∪ A.filter (fun i => i = t) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hi, h⟩
      rcases (show i.val < t.val ∨ i.val = t.val by omega) with h | h
      · exact Or.inl ⟨hi, h⟩
      · exact Or.inr ⟨hi, Fin.ext h⟩
    · rintro (⟨hi, h⟩ | ⟨hi, h⟩)
      · exact ⟨hi, by omega⟩
      · rw [h]
        exact ⟨h ▸ hi, by omega⟩
  have hd : Disjoint (A.filter (fun i => i.val < t.val)) (A.filter (fun i => i = t)) := by
    rw [Finset.disjoint_filter]
    intro i _ h1 h2
    rw [h2] at h1
    exact Nat.lt_irrefl _ h1
  rw [e, Finset.card_union_of_disjoint hd, Finset.filter_eq']
  split_ifs <;> simp
theorem pC_xor (a b : Bool) : (!(!(a && !(a && b)) && !(b && !(a && b)))) = xor a b := by
  cases a <;> cases b <;> rfl
theorem pC_and3 (x y z : Bool) : (x && (y && z)) = (y && (z && x)) := by
  cases x <;> cases y <;> cases z <;> rfl
theorem pC_sum (k : ℕ) (A : Finset (Fin k)) (t : Fin k) (j : Fin (wd k)) :
    zA k A (cntW k t j 3) = (cntA k A (t.val + 1)).testBit j.val := by
  have h : zA k A (cntW k t j 3) = xor ((cntA k A t.val).testBit j.val) (carA k A t j.val) :=
    pC_xor ((cntA k A t.val).testBit j.val) (carA k A t j.val)
  rw [h, pC_cnt_succ]
  by_cases ht : t ∈ A
  · have hc : carA k A t j.val = decide (∀ i, i < j.val → (cntA k A t.val).testBit i = true) := by
      simp [carA, ht]
    rw [hc, ite_eq_left ht, pC_inc]
  · have hc : carA k A t j.val = false := by
      simp [carA, ht]
    rw [hc, ite_eq_right ht, Nat.add_zero, Bool.xor_false]
theorem pC_reg (k : ℕ) (A : Finset (Fin k)) (t : ℕ) (ht : t ≤ k) (j : Fin (wd k)) :
    zA k A (regW k t j) = (cntA k A t).testBit j.val := by
  cases t with
  | zero =>
    have e : regW k 0 j = fW k := rfl
    rw [e, pC_cnt_zero, Nat.zero_testBit]
    rfl
  | succ s =>
    have hs : s < k := by omega
    have e : regW k (s+1) j = cntW k ⟨s, hs⟩ j 3 := by simp [regW, hs]
    rw [e]
    exact pC_sum k A ⟨s, hs⟩ j
theorem pC_car (k : ℕ) (A : Finset (Fin k)) (t : Fin k) (j : Fin (wd k)) :
    zA k A (carW k t j) = carA k A t j.val := by
  rcases j with ⟨jv, hj⟩
  cases jv with
  | zero =>
    have e : carW k t ⟨0, hj⟩ = inpW k t := rfl
    rw [e]
    simp [zA, inpW, valA, carA]
  | succ m =>
    have hm : m < wd k := by omega
    have e : carW k t ⟨m+1, hj⟩ = negW k (cntW k t ⟨m, hm⟩ 0) := by simp [carW]
    have h1 : zA k A (negW k (cntW k t ⟨m, hm⟩ 0)) =
        (!(!((cntA k A t.val).testBit m && carA k A t m))) := rfl
    rw [e, h1, Bool.not_not]
    show ((cntA k A t.val).testBit m &&
        (decide (t ∈ A) && decide (∀ i, i < m → (cntA k A t.val).testBit i = true))) =
      (decide (t ∈ A) && decide (∀ i, i < m + 1 → (cntA k A t.val).testBit i = true))
    rw [pC_dec_succ]
    exact pC_and3 _ _ _
theorem valA_good (k : ℕ) (A : Finset (Fin k)) : GoodZ k (zA k A) := by
  unfold GoodZ
  refine ⟨fun u => rfl, ?_⟩
  intro g
  rcases g with e | ⟨t, j, q⟩
  · rfl
  · have hr := pC_reg k A t.val (Nat.le_of_lt t.isLt) j
    have hc := pC_car k A t j
    rcases q with ⟨q, hq⟩
    interval_cases q
    · show zA k A (goutW k (Sum.inr (t, j, _))) =
        !(zA k A (regW k t.val j) && zA k A (carW k t j))
      rw [hr, hc]
      rfl
    · show zA k A (goutW k (Sum.inr (t, j, _))) =
        !(zA k A (regW k t.val j) && zA k A (cntW k t j 0))
      rw [hr]
      rfl
    · show zA k A (goutW k (Sum.inr (t, j, _))) =
        !(zA k A (carW k t j) && zA k A (cntW k t j 0))
      rw [hc]
      rfl
    · rfl
theorem valA_rail (k : ℕ) (hk : 1 ≤ k) (A : Finset (Fin k)) (j : Fin (wd k)) :
    zA k A (regW k k j) = A.card.testBit j.val := by
  have _hk := hk
  rw [pC_reg k A k (Nat.le_refl k) j, pC_cnt_k]
theorem pD_zA_fW (k : ℕ) (A : Finset (Fin k)) : zA k A (fW k) = false := by
  simp [zA, fW, valA]
theorem pD_zA_inp (k : ℕ) (A : Finset (Fin k)) (i : Fin k) :
    zA k A (inpW k i) = decide (i ∈ A) := by
  simp [zA, inpW, valA]
theorem pD_gIn0 (k : ℕ) (t : Fin k) (j : Fin (wd k)) :
    gIn k (Sum.inr (t, j, 0)) = (regW k t.val j, carW k t j) := rfl
theorem pD_gIn1 (k : ℕ) (t : Fin k) (j : Fin (wd k)) :
    gIn k (Sum.inr (t, j, 1)) = (regW k t.val j, cntW k t j 0) := rfl
theorem pD_gIn2 (k : ℕ) (t : Fin k) (j : Fin (wd k)) :
    gIn k (Sum.inr (t, j, 2)) = (carW k t j, cntW k t j 0) := rfl
theorem pD_gIn3 (k : ℕ) (t : Fin k) (j : Fin (wd k)) :
    gIn k (Sum.inr (t, j, 3)) = (cntW k t j 1, cntW k t j 2) := rfl
theorem good_unique (k : ℕ) (A : Finset (Fin k)) (z : Wire k → Bool) (hF : z (fW k) = false)
    (hG : GoodZ k z) (hin : ∀ i, z (inpW k i) = decide (i ∈ A)) : ∀ x, z x = zA k A x := by
  have hV := valA_good k A
  have hneg : ∀ x : Wire k, z x = zA k A x → z (negW k x) = zA k A (negW k x) := by
    rintro ⟨b, u⟩ h
    have e1 := hG.1 u
    have e2 := hV.1 u
    cases b
    · show z (true, u) = zA k A (true, u)
      rw [e1, e2] at h
      revert h
      cases z (true, u) <;> cases zA k A (true, u) <;> simp
    · show z (false, u) = zA k A (false, u)
      rw [e1, e2, h]
  have hfW : z (fW k) = zA k A (fW k) := hF.trans (pD_zA_fW k A).symm
  have hinp : ∀ i, z (inpW k i) = zA k A (inpW k i) := fun i => (hin i).trans (pD_zA_inp k A i).symm
  have hgate : ∀ g : Gate k, z (gIn k g).1 = zA k A (gIn k g).1 →
      z (gIn k g).2 = zA k A (gIn k g).2 → z (goutW k g) = zA k A (goutW k g) := by
    intro g h1 h2
    rw [hG.2 g, hV.2 g, h1, h2]
  have hreg : ∀ (t : Fin k) (j : Fin (wd k)),
      (0 < t.val → z (cntW k ⟨t.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) t.isLt⟩ j 3) =
        zA k A (cntW k ⟨t.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) t.isLt⟩ j 3)) →
      z (regW k t.val j) = zA k A (regW k t.val j) := by
    intro t j h
    unfold regW
    split_ifs with ht
    · exact h ht.1
    · exact hfW
  have hcar : ∀ (t : Fin k) (j : Fin (wd k)),
      (0 < j.val → z (cntW k t ⟨j.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) j.isLt⟩ 0) =
        zA k A (cntW k t ⟨j.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) j.isLt⟩ 0)) →
      z (carW k t j) = zA k A (carW k t j) := by
    intro t j h
    unfold carW
    split_ifs with hj
    · exact hneg _ (h hj)
    · exact hinp t
  have hstep : ∀ (t : Fin k) (j : Fin (wd k)), z (regW k t.val j) = zA k A (regW k t.val j) →
      z (carW k t j) = zA k A (carW k t j) →
      ∀ q : Fin 4, z (cntW k t j q) = zA k A (cntW k t j q) := by
    intro t j hr hc
    have h0 : z (cntW k t j 0) = zA k A (cntW k t j 0) :=
      hgate (Sum.inr (t, j, 0)) (by rw [pD_gIn0]; exact hr) (by rw [pD_gIn0]; exact hc)
    have h1 : z (cntW k t j 1) = zA k A (cntW k t j 1) :=
      hgate (Sum.inr (t, j, 1)) (by rw [pD_gIn1]; exact hr) (by rw [pD_gIn1]; exact h0)
    have h2 : z (cntW k t j 2) = zA k A (cntW k t j 2) :=
      hgate (Sum.inr (t, j, 2)) (by rw [pD_gIn2]; exact hc) (by rw [pD_gIn2]; exact h0)
    have h3 : z (cntW k t j 3) = zA k A (cntW k t j 3) :=
      hgate (Sum.inr (t, j, 3)) (by rw [pD_gIn3]; exact h1) (by rw [pD_gIn3]; exact h2)
    intro q
    rcases q with ⟨_ | _ | _ | _ | n, hn⟩
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact absurd hn (by omega)
  have hinner : ∀ t : Fin k, (∀ j, z (regW k t.val j) = zA k A (regW k t.val j)) →
      ∀ j q, z (cntW k t j q) = zA k A (cntW k t j q) := by
    intro t hR
    have hJ : ∀ (jn : ℕ) (j : Fin (wd k)), j.val = jn →
        ∀ q, z (cntW k t j q) = zA k A (cntW k t j q) := by
      intro jn
      induction jn with
      | zero =>
        intro j hj
        exact hstep t j (hR j) (hcar t j (fun h => absurd h (by omega)))
      | succ jn ihj =>
        intro j hj
        exact hstep t j (hR j) (hcar t j (fun _ =>
          ihj ⟨j.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) j.isLt⟩ (by show j.val - 1 = jn; omega) 0))
    intro j
    exact hJ j.val j rfl
  have hall : ∀ (tn : ℕ) (t : Fin k), t.val = tn →
      ∀ j q, z (cntW k t j q) = zA k A (cntW k t j q) := by
    intro tn
    induction tn with
    | zero =>
      intro t ht
      exact hinner t (fun j => hreg t j (fun h => absurd h (by omega)))
    | succ tn iht =>
      intro t ht
      exact hinner t (fun j => hreg t j (fun _ =>
        iht ⟨t.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) t.isLt⟩ (by show t.val - 1 = tn; omega) j 3))
  have hbase : ∀ u : W0 k, z (true, u) = zA k A (true, u) := by
    intro u
    rcases u with ⟨⟩ | i | e | ⟨t, j, q⟩
    · exact hneg (fW k) hfW
    · exact hinp i
    · exact hgate (Sum.inl e) (hinp e.1.1) (hinp e.1.2)
    · exact hall t.val t rfl j q
  intro x
  rcases x with ⟨b, u⟩
  cases b
  · exact hneg (true, u) (hbase u)
  · exact hbase u
theorem pD_regW_k (k : ℕ) (hk : 1 ≤ k) (j : Fin (wd k)) :
    regW k k j = cntW k ⟨k - 1, by omega⟩ j 3 := by
  have h : 0 < k ∧ k - 1 < k := ⟨by omega, by omega⟩
  rw [regW, dite_eq_left h]
def pD_dec (k : ℕ) (d : Fin k ⊕ (Ed k ⊕ (Bool × Fin (wd k)))) :
    Wire k → Fin k ⊕ (Ed k ⊕ (Bool × Fin (wd k)))
  | (_, Sum.inr (Sum.inl i)) => Sum.inl i
  | (_, Sum.inr (Sum.inr (Sum.inl e))) => Sum.inr (Sum.inl e)
  | (b, Sum.inr (Sum.inr (Sum.inr (_, j, _)))) => Sum.inr (Sum.inr (!b, j))
  | (_, Sum.inl _) => d
theorem pD_dec_port (k : ℕ) (hk : 1 ≤ k) (d : Fin k ⊕ (Ed k ⊕ (Bool × Fin (wd k))))
    (l : Fin k ⊕ (Ed k ⊕ (Bool × Fin (wd k)))) : pD_dec k d (portW k l) = l := by
  rcases l with i | e | ⟨b, j⟩
  · rfl
  · rfl
  · show pD_dec k d (flipW k b (regW k k j)) = Sum.inr (Sum.inr (b, j))
    rw [pD_regW_k k hk]
    cases b <;> rfl
theorem portW_inj (k : ℕ) (hk : 1 ≤ k) : Function.Injective (portW k) := by
  intro l l' h
  have h2 := congrArg (pD_dec k l) h
  rwa [pD_dec_port k hk, pD_dec_port k hk] at h2
def pD_one (k : ℕ) : Wire k → Bool
  | (_, Sum.inl _) => true
  | (_, Sum.inr _) => false
theorem portW_ne (k : ℕ) (hk : 1 ≤ k) (l : Fin k ⊕ (Ed k ⊕ (Bool × Fin (wd k)))) :
    portW k l ≠ fW k := by
  intro h
  have h2 := congrArg (pD_one k) h
  rcases l with i | e | ⟨b, j⟩
  · exact Bool.false_ne_true h2
  · exact Bool.false_ne_true h2
  · have h3 : pD_one k (flipW k b (regW k k j)) = pD_one k (fW k) := h2
    rw [pD_regW_k k hk] at h3
    exact Bool.false_ne_true h3
theorem fD_dartOf (k : ℕ) (x : Wire k) : fD k (dartOf k x) = x := by
  rcases x with ⟨p, u⟩
  cases p <;> simp [fD, dartOf, ends0, flipW]
theorem dartOf_inj (k : ℕ) : Function.Injective (dartOf k) := by
  intro x y h
  have := congrArg (fD k) h
  simpa [fD_dartOf] using this
noncomputable def piD (k : ℕ) : Equiv.Perm (Dart k) := Classical.choose (orbit_perm (fD k))
theorem piD_spec (k : ℕ) : (∀ d, fD k (piD k d) = fD k d) ∧
    ∀ g : Dart k → Bool, (∀ d, g (piD k d) = g d) → ∀ d d', fD k d = fD k d' → g d = g d' :=
  Classical.choose_spec (orbit_perm (fD k))
noncomputable def eqvD (k : ℕ) : Dart k ≃ Fin (Fintype.card (Dart k)) := Fintype.equivFin (Dart k)
noncomputable def Pm (k : ℕ) : Fin 3 → Equiv.Perm (Dart k) := ![1, piD k, alphaD k]
noncomputable def Mm (k : ℕ) (j : Fin 3) : Equiv.Perm (Fin (Fintype.card (Dart k))) :=
  (eqvD k).symm.trans ((Pm k j).trans (eqvD k))
noncomputable def portV (k : ℕ) (l : Fin k ⊕ (Ed k ⊕ (Bool × Fin (wd k)))) :
    Bool × Fin (Fintype.card (Dart k)) :=
  (false, eqvD k (dartOf k (portW k l)))
noncomputable def pinsV (k : ℕ) : Finset (Bool × Fin (Fintype.card (Dart k))) :=
  {(false, eqvD k (dartOf k (fW k)))}
theorem portV_inj (k : ℕ) (hk : 1 ≤ k) : Function.Injective (portV k) := by
  intro l l' h
  simp only [portV, Prod.mk.injEq, true_and, EmbeddingLike.apply_eq_iff_eq] at h
  exact portW_inj k hk (dartOf_inj k h)
theorem Pm0 (k : ℕ) : Pm k 0 = 1 := rfl
theorem Pm1 (k : ℕ) : Pm k 1 = piD k := rfl
theorem Pm2 (k : ℕ) : Pm k 2 = alphaD k := rfl
theorem cost_eq (k : ℕ) (y : Bool × Fin (Fintype.card (Dart k)) → Bool) (j : Fin 3) :
    (Finset.univ.filter (fun i => y (false, i) ≠ y (true, Mm k j i))).card =
    (Finset.univ.filter (fun d : Dart k => y (false, eqvD k d) ≠ y (true, eqvD k (Pm k j d)))).card :=
  cost_transport (eqvD k) (Pm k j) y
theorem zA_flip (k : ℕ) (A : Finset (Fin k)) (b : Bool) (x : Wire k) :
    zA k A (flipW k b x) = xor b (zA k A x) := by
  rcases x with ⟨p, u⟩
  cases b <;> cases p <;> simp [zA, flipW]
theorem zA_fW (k : ℕ) (A : Finset (Fin k)) : zA k A (fW k) = false := by
  simp [zA, fW, valA]
theorem wire_const (k : ℕ) (y : Bool × Fin (Fintype.card (Dart k)) → Bool)
    (h0 : (Finset.univ.filter (fun i => y (false, i) ≠ y (true, Mm k 0 i))).card = 0)
    (h1 : (Finset.univ.filter (fun i => y (false, i) ≠ y (true, Mm k 1 i))).card = 0) :
    ∀ b d, y (b, eqvD k d) = y (false, eqvD k (dartOf k (fD k d))) := by
  rw [cost_eq, Pm0, Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h0
  rw [cost_eq, Pm1, Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h1
  have e0 : ∀ d, y (false, eqvD k d) = y (true, eqvD k d) := by
    intro d
    have := h0 (Finset.mem_univ d)
    simpa using this
  have e1 : ∀ d, y (false, eqvD k (piD k d)) = y (false, eqvD k d) := by
    intro d
    have := h1 (Finset.mem_univ d)
    simp only [ne_eq, not_not] at this
    rw [e0 (piD k d)]
    exact this.symm
  have key : ∀ d d', fD k d = fD k d' → y (false, eqvD k d) = y (false, eqvD k d') :=
    (piD_spec k).2 (fun d => y (false, eqvD k d)) e1
  intro b d
  have hd := key d (dartOf k (fD k d)) (fD_dartOf k (fD k d)).symm
  cases b
  · exact hd
  · rw [← e0 d]
    exact hd
theorem feas_char (k : ℕ) (y : Bool × Fin (Fintype.card (Dart k)) → Bool)
    (hpin : y (false, eqvD k (dartOf k (fW k))) = false)
    (h0 : (Finset.univ.filter (fun i => y (false, i) ≠ y (true, Mm k 0 i))).card = 0)
    (h1 : (Finset.univ.filter (fun i => y (false, i) ≠ y (true, Mm k 1 i))).card = 0)
    (h2 : (Finset.univ.filter (fun i => y (false, i) ≠ y (true, Mm k 2 i))).card = Tv k) :
    GoodZ k (fun x => y (false, eqvD k (dartOf k x))) ∧
    ∀ b d, y (b, eqvD k d) = y (false, eqvD k (dartOf k (fD k d))) := by
  have hw := wire_const k y h0 h1
  refine ⟨?_, hw⟩
  apply (cut_iff k (fun x => y (false, eqvD k (dartOf k x))) hpin).1
  rw [cost_eq, Pm2] at h2
  rw [← h2]
  congr 1
  apply Finset.filter_congr
  intro d _
  simp only [hw false d, hw true (alphaD k d)]
theorem feas_eq (k : ℕ) (A : Finset (Fin k)) (y : Bool × Fin (Fintype.card (Dart k)) → Bool)
    (hpin : y (false, eqvD k (dartOf k (fW k))) = false)
    (h0 : (Finset.univ.filter (fun i => y (false, i) ≠ y (true, Mm k 0 i))).card = 0)
    (h1 : (Finset.univ.filter (fun i => y (false, i) ≠ y (true, Mm k 1 i))).card = 0)
    (h2 : (Finset.univ.filter (fun i => y (false, i) ≠ y (true, Mm k 2 i))).card = Tv k)
    (hin : ∀ i, y (portV k (Sum.inl i)) = decide (i ∈ A)) :
    ∀ b d, y (b, eqvD k d) = zA k A (fD k d) := by
  obtain ⟨hG, hw⟩ := feas_char k y hpin h0 h1 h2
  have hz := good_unique k A (fun x => y (false, eqvD k (dartOf k x))) hpin hG (fun i => hin i)
  intro b d
  rw [hw b d]
  exact hz (fD k d)
theorem yA_good (k : ℕ) (A : Finset (Fin k)) :
    let y : Bool × Fin (Fintype.card (Dart k)) → Bool := fun v => zA k A (fD k ((eqvD k).symm v.2))
    (Finset.univ.filter (fun i => y (false, i) ≠ y (true, Mm k 0 i))).card = 0 ∧
    (Finset.univ.filter (fun i => y (false, i) ≠ y (true, Mm k 1 i))).card = 0 ∧
    (Finset.univ.filter (fun i => y (false, i) ≠ y (true, Mm k 2 i))).card = Tv k := by
  intro y
  refine ⟨?_, ?_, ?_⟩
  · rw [cost_eq, Pm0, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro d _
    simp [y]
  · rw [cost_eq, Pm1, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro d _
    simp [y, (piD_spec k).1 d]
  · rw [cost_eq, Pm2]
    rw [← (cut_iff k (zA k A) (zA_fW k A)).2 (valA_good k A)]
    congr 1
    apply Finset.filter_congr
    intro d _
    simp [y]
theorem assembly (k : ℕ) (hk : 1 ≤ k) (G : Ed k → Bool) (s : ℕ) (hs : s ≤ k) :
    let n := Fintype.card (Dart k)
    let cost := fun (y : Bool × Fin n → Bool) (j : Fin 3) =>
      (Finset.univ.filter (fun i : Fin n => y (false,i) ≠ y (true, Mm k j i))).card
    let feasible := (Finset.univ : Finset (Bool × Fin n → Bool)).filter (fun y =>
      (∀ u ∈ pinsV k, y u = false) ∧
      (∀ e : Ed k, G e = false → y (portV k (Sum.inr (Sum.inl e))) = false) ∧
      (∀ j : Fin (wd k), y (portV k (Sum.inr (Sum.inr (s.testBit j.val,j)))) = false) ∧
      cost y 0 = 0 ∧ cost y 1 = 0 ∧ cost y 2 = Tv k)
    (∀ y ∈ feasible, (Finset.univ.filter (fun u : Bool × Fin n => y u = true)).card = n) ∧
    ∀ A : Finset (Fin k),
      (feasible.filter (fun y => ∀ i, y (portV k (Sum.inl i)) = decide (i ∈ A))).card =
        if A.card = s ∧ (∀ e : Ed k, e.val.1 ∈ A → e.val.2 ∈ A → G e = true)
        then 1 else 0 := by
  dsimp only
  refine ⟨?_, ?_⟩
  · intro y hy
    rw [Finset.mem_filter] at hy
    obtain ⟨-, hp, -, -, h0, h1, h2⟩ := hy
    obtain ⟨hG, hw⟩ := feas_char k y (hp _ (Finset.mem_singleton_self _)) h0 h1 h2
    rw [true_transport (eqvD k) y]
    refine Eq.trans ?_ (half_true k (fun x => y (false, eqvD k (dartOf k x))) hG.1)
    congr 1
    apply Finset.filter_congr
    intro u _
    rw [hw u.1 u.2]
  · intro A
    split_ifs with hc
    · rw [Finset.card_eq_one]
      refine ⟨fun v => zA k A (fD k ((eqvD k).symm v.2)), ?_⟩
      ext y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨hp, -, -, h0, h1, h2⟩, hin⟩
        have hy := feas_eq k A y (hp _ (Finset.mem_singleton_self _)) h0 h1 h2 hin
        funext v
        rcases v with ⟨b, i⟩
        have := hy b ((eqvD k).symm i)
        simpa using this
      · rintro rfl
        obtain ⟨h0, h1, h2⟩ := yA_good k A
        refine ⟨⟨?_, ?_, ?_, h0, h1, h2⟩, ?_⟩
        · intro u hu
          simp only [pinsV, Finset.mem_singleton] at hu
          subst hu
          simp [fD_dartOf, zA_fW]
        · intro e he
          have hne : ¬ (e.val.1 ∈ A ∧ e.val.2 ∈ A) := fun h => by
            have := hc.2 e h.1 h.2
            rw [he] at this
            exact Bool.false_ne_true this
          simp [portV, fD_dartOf, portW, zA, negW, goutW, valA]
          tauto
        · intro j
          simp only [portV, Equiv.symm_apply_apply, fD_dartOf, portW, zA_flip, valA_rail k hk A j, hc.1]
          simp
        · intro i
          simp [portV, fD_dartOf, portW, zA, inpW, valA]
    · by_contra hne
      obtain ⟨y, hy⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hne)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
      obtain ⟨⟨hp, hGe, hr, h0, h1, h2⟩, hin⟩ := hy
      have hy := feas_eq k A y (hp _ (Finset.mem_singleton_self _)) h0 h1 h2 hin
      apply hc
      constructor
      · rw [card_eq_iff_bits k A s hs]
        intro j
        have := hr j
        simp only [portV, hy, fD_dartOf, portW, zA_flip, valA_rail k hk A j] at this
        revert this
        cases s.testBit j.val <;> cases A.card.testBit j.val <;> simp
      · intro e h1 h2
        by_contra hne
        have := hGe e (by simpa using hne)
        simp [portV, hy, fD_dartOf, portW, zA, negW, goutW, valA, h1, h2] at this
end PEqualNP.Outside.L_pcx_364
theorem PEqualNP.Outside.L_pcx_364 : ∀ k : ℕ, 1 ≤ k →
  let E := {p : Fin k × Fin k // p.1 < p.2}
  let w := 1 + Nat.log 2 (k+1)
  let Labels := Fin k ⊕ (E ⊕ (Bool × Fin w))
  ∃ n : ℕ, n ≤ 512*(k+1)^2 ∧
    let V := Bool × Fin n
    let X := V → Bool
    ∃ (M : Fin 3 → Equiv.Perm (Fin n)) (T : ℕ) (port : Labels ↪ V)
      (pins : Finset V), pins.card ≤ 2 ∧ (∀ j, port j ∉ pins) ∧
      ∀ (G : E → Bool) (s : ℕ), s ≤ k →
        let cost := fun (y : X) (j : Fin 3) =>
          (Finset.univ.filter (fun i : Fin n => y (false,i) ≠ y (true,M j i))).card
        let feasible := (Finset.univ : Finset X).filter (fun y =>
          (∀ u ∈ pins, y u = false) ∧
          (∀ e : E, G e = false → y (port (Sum.inr (Sum.inl e))) = false) ∧
          (∀ j : Fin w, y (port (Sum.inr (Sum.inr (s.testBit j.val,j)))) = false) ∧
          cost y 0 = 0 ∧ cost y 1 = 0 ∧ cost y 2 = T)
        (∀ y ∈ feasible, (Finset.univ.filter (fun u : V => y u = true)).card = n) ∧
        ∀ A : Finset (Fin k),
          (feasible.filter (fun y => ∀ i, y (port (Sum.inl i)) = decide (i ∈ A))).card =
            if A.card = s ∧ (∀ e : E, e.val.1 ∈ A → e.val.2 ∈ A → G e = true)
            then 1 else 0 := by
  intro k hk E w Labels
  refine ⟨Fintype.card (PEqualNP.Outside.L_pcx_364.Dart k), PEqualNP.Outside.L_pcx_364.card_le k, ?_⟩
  intro V X
  refine ⟨PEqualNP.Outside.L_pcx_364.Mm k, PEqualNP.Outside.L_pcx_364.Tv k,
    ⟨PEqualNP.Outside.L_pcx_364.portV k, PEqualNP.Outside.L_pcx_364.portV_inj k hk⟩,
    PEqualNP.Outside.L_pcx_364.pinsV k, ?_, ?_, ?_⟩
  · simp [PEqualNP.Outside.L_pcx_364.pinsV]
  · intro j hj
    have h1 : PEqualNP.Outside.L_pcx_364.portV k j = (false, PEqualNP.Outside.L_pcx_364.eqvD k
        (PEqualNP.Outside.L_pcx_364.dartOf k (PEqualNP.Outside.L_pcx_364.fW k))) :=
      Finset.mem_singleton.mp hj
    have h2 := congrArg (fun p => (PEqualNP.Outside.L_pcx_364.eqvD k).symm p.2) h1
    simp only [PEqualNP.Outside.L_pcx_364.portV, Equiv.symm_apply_apply] at h2
    exact PEqualNP.Outside.L_pcx_364.portW_ne k hk j (PEqualNP.Outside.L_pcx_364.dartOf_inj k h2)
  · intro G s hs
    exact PEqualNP.Outside.L_pcx_364.assembly k hk G s hs
