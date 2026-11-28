import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_368

lemma rot_const : ∀ (n : ℕ) (h : Fin n → Bool), (∀ a, h (finRotate n a) = h a) →
    ∀ a b, h a = h b := by
  intro n
  cases n with
  | zero => intro h _ a; exact a.elim0
  | succ n =>
    intro h hh
    have key : ∀ a : Fin (n+1), h a = h 0 := by
      intro a
      induction a using Fin.induction with
      | zero => rfl
      | succ i ih =>
        have h1 : finRotate (n + 1) i.castSucc = i.succ := finRotate_of_lt i.isLt
        have := hh i.castSucc
        rw [h1] at this
        rw [this, ih]
    intro a b
    rw [key a, key b]

lemma exists_cyc {T L : Type} [Fintype T] [DecidableEq L] (lit : T → L) :
    ∃ σ : Equiv.Perm T, (∀ t, lit (σ t) = lit t) ∧
      ∀ f : T → Bool, (∀ t, f (σ t) = f t) → ∀ t t', lit t = lit t' → f t = f t' := by
  classical
  let E : T ≃ Σ ℓ : L, Fin (Fintype.card {t // lit t = ℓ}) :=
    (Equiv.sigmaFiberEquiv lit).symm.trans (Equiv.sigmaCongrRight fun ℓ => Fintype.equivFin _)
  let ρ : Equiv.Perm (Σ ℓ : L, Fin (Fintype.card {t // lit t = ℓ})) :=
    Equiv.sigmaCongrRight fun ℓ => finRotate _
  have hE : ∀ t, (E t).1 = lit t := fun t => rfl
  have hρ : ∀ p, (ρ p).1 = p.1 := fun p => rfl
  refine ⟨E.trans (ρ.trans E.symm), ?_, ?_⟩
  · intro t
    rw [← hE, ← hE t]
    simp [hρ]
  · intro f hf
    have key : ∀ p q : (Σ ℓ : L, Fin (Fintype.card {t // lit t = ℓ})), p.1 = q.1 →
        f (E.symm p) = f (E.symm q) := by
      rintro ⟨ℓ, a⟩ ⟨ℓ', b⟩ h
      obtain rfl : ℓ = ℓ' := h
      refine rot_const _ (fun a => f (E.symm ⟨ℓ, a⟩)) ?_ a b
      intro a
      have := hf (E.symm ⟨ℓ, a⟩)
      simpa [ρ] using this
    intro t t' h
    have := key (E t) (E t') (by rw [hE, hE, h])
    simpa using this

lemma b4 : ∀ p q p' q' : Bool, (if p ≠ q then 1 else 0) ≤
    (if p' ≠ q' then 1 else 0) + (if p ≠ p' then 1 else 0) + (if q ≠ q' then 1 else 0) := by
  decide

lemma fib {α L : Type} [Fintype α] [Fintype L] [DecidableEq L] (f : α → L) (P : α → Prop)
    [DecidablePred P] :
    (Finset.univ.filter P).card =
      ∑ ℓ : L, (Finset.univ.filter (fun a => f a = ℓ ∧ P a)).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := f) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [Finset.filter_filter]
  congr 1
  ext a
  simp [and_comm]

lemma dbl {T : Type} [Fintype T] (P : T → Prop) [DecidablePred P] :
    (Finset.univ.filter (fun u : Bool × T => P u.2)).card = 2 * (Finset.univ.filter P).card := by
  rw [Finset.card_filter, Finset.card_filter, Fintype.sum_prod_type, Fintype.sum_bool, two_mul]

lemma tri_ineq {α : Type} [Fintype α] (Y Z W : α → Bool) :
    (Finset.univ.filter (fun u => Y u ≠ W u)).card ≤
      (Finset.univ.filter (fun u => Y u ≠ Z u)).card +
        (Finset.univ.filter (fun u => Z u ≠ W u)).card := by
  classical
  refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
  intro u hu
  rw [Finset.mem_filter] at hu
  rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
  by_cases h : Y u = Z u
  · right; exact ⟨Finset.mem_univ _, fun h' => hu.2 (h.trans h')⟩
  · left; exact ⟨Finset.mem_univ _, h⟩

lemma lips {T : Type} [Fintype T] (π : Equiv.Perm T) (Y Y' : Bool × T → Bool) :
    (Finset.univ.filter (fun t : T => Y (false, t) ≠ Y (true, π t))).card ≤
      (Finset.univ.filter (fun t : T => Y' (false, t) ≠ Y' (true, π t))).card +
        (Finset.univ.filter (fun u : Bool × T => Y u ≠ Y' u)).card := by
  rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, Fintype.sum_prod_type,
    Fintype.sum_bool,
    ← Equiv.sum_comp π (fun t => if Y (true, t) ≠ Y' (true, t) then 1 else 0),
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun t _ => ?_
  have := b4 (Y (false, t)) (Y (true, π t)) (Y' (false, t)) (Y' (true, π t))
  omega

def fl {T L : Type} [Fintype T] [DecidableEq L] (lit : T → L) (Y : Bool × T → Bool) (ℓ : L)
    (w : Bool) : ℕ :=
  (Finset.univ.filter (fun u : Bool × T => lit u.2 = ℓ ∧ Y u ≠ w)).card

def maj {T L : Type} [Fintype T] [DecidableEq L] (lit : T → L) (Y : Bool × T → Bool) (ℓ : L) :
    Bool :=
  decide (fl lit Y ℓ true ≤ fl lit Y ℓ false)

def dfc {T L : Type} [Fintype T] [DecidableEq L] (lit : T → L) (π : Equiv.Perm T)
    (Y : Bool × T → Bool) (ℓ : L) : ℕ :=
  (Finset.univ.filter (fun t : T => lit t = ℓ ∧ Y (false, t) ≠ Y (true, π t))).card

lemma fl_add {T L : Type} [Fintype T] [DecidableEq L] (lit : T → L) (Y : Bool × T → Bool)
    (ℓ : L) :
    fl lit Y ℓ true + fl lit Y ℓ false =
      2 * (Finset.univ.filter (fun t : T => lit t = ℓ)).card := by
  unfold fl
  rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, Fintype.sum_prod_type,
    Fintype.sum_prod_type, Fintype.sum_bool, Fintype.sum_bool, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  by_cases h : lit t = ℓ <;> cases Y (true, t) <;> cases Y (false, t) <;> simp [h]

lemma fl_maj_le {T L : Type} [Fintype T] [DecidableEq L] (lit : T → L) (Y : Bool × T → Bool)
    (ℓ : L) (w : Bool) : fl lit Y ℓ (maj lit Y ℓ) ≤ fl lit Y ℓ w := by
  unfold maj
  by_cases h : fl lit Y ℓ true ≤ fl lit Y ℓ false
  · rw [decide_eq_true h]
    cases w
    · exact h
    · exact le_rfl
  · rw [decide_eq_false h]
    cases w
    · exact le_rfl
    · omega

lemma fl_zero_of {T L : Type} [Fintype T] [DecidableEq L] (lit : T → L) (σ : Equiv.Perm T)
    (hlit : ∀ t, lit (σ t) = lit t)
    (htr : ∀ f : T → Bool, (∀ t, f (σ t) = f t) → ∀ t t', lit t = lit t' → f t = f t')
    (Y : Bool × T → Bool) (ℓ : L)
    (h0 : ∀ t, lit t = ℓ → Y (false, t) = Y (true, t))
    (h1 : ∀ t, lit t = ℓ → Y (false, t) = Y (true, σ t)) :
    fl lit Y ℓ (maj lit Y ℓ) = 0 := by
  have hc : ∀ t t', lit t = ℓ → lit t' = ℓ → Y (true, t) = Y (true, t') := by
    intro t t' ht ht'
    have := htr (fun t => if lit t = ℓ then Y (true, t) else false) (by
      intro t
      by_cases h : lit t = ℓ
      · simp only [hlit, h, ite_true]
        rw [← h1 t h, h0 t h]
      · simp [hlit, h]) t t' (by rw [ht, ht'])
    simpa [ht, ht'] using this
  by_cases hex : ∃ t0, lit t0 = ℓ
  · obtain ⟨t0, ht0⟩ := hex
    have : fl lit Y ℓ (Y (true, t0)) = 0 := by
      unfold fl
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro ⟨b, t⟩ - ⟨hl, hne⟩
      apply hne
      cases b
      · rw [h0 t hl]
        exact hc t t0 hl ht0
      · exact hc t t0 hl ht0
    have := fl_maj_le lit Y ℓ (Y (true, t0))
    omega
  · have : fl lit Y ℓ true = 0 := by
      unfold fl
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro ⟨b, t⟩ - ⟨hl, -⟩
      exact hex ⟨t, hl⟩
    have := fl_maj_le lit Y ℓ true
    omega

lemma dfc_even {T L : Type} [Fintype T] [DecidableEq L] (lit : T → L) (σ : Equiv.Perm T)
    (hlit : ∀ t, lit (σ t) = lit t) (Y : Bool × T → Bool) (ℓ : L) :
    Even (dfc lit (Equiv.refl T) Y ℓ + dfc lit σ Y ℓ) := by
  have hS : (∑ t : T, (if lit t = ℓ then (if Y (true, σ t) = true then 1 else 0) else 0) : ℕ) =
      ∑ t : T, (if lit t = ℓ then (if Y (true, t) = true then 1 else 0) else 0) := by
    rw [← Equiv.sum_comp σ
      (fun t => if lit t = ℓ then (if Y (true, t) = true then 1 else 0) else 0)]
    simp only [hlit]
  have hE : Even ((dfc lit (Equiv.refl T) Y ℓ + dfc lit σ Y ℓ) +
      ((∑ t : T, (if lit t = ℓ then (if Y (true, t) = true then 1 else 0) else 0) : ℕ) +
        ∑ t : T, (if lit t = ℓ then (if Y (true, σ t) = true then 1 else 0) else 0))) := by
    unfold dfc
    rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.even_sum _ fun t _ => ?_
    by_cases h : lit t = ℓ
    · simp only [h, true_and, ite_true, Equiv.refl_apply]
      cases Y (false, t) <;> cases Y (true, t) <;> cases Y (true, σ t) <;> decide
    · simp [h]
  rw [hS] at hE
  exact (Nat.even_add.mp hE).mpr ⟨_, rfl⟩

lemma class_bound {T L : Type} [Fintype T] [DecidableEq L] (lit : T → L) (σ : Equiv.Perm T)
    (hlit : ∀ t, lit (σ t) = lit t)
    (htr : ∀ f : T → Bool, (∀ t, f (σ t) = f t) → ∀ t t', lit t = lit t' → f t = f t')
    (Y : Bool × T → Bool) (ℓ : L) (K : ℕ)
    (hK : (Finset.univ.filter (fun t : T => lit t = ℓ)).card ≤ K) :
    2 * fl lit Y ℓ (maj lit Y ℓ) ≤ K * (dfc lit (Equiv.refl T) Y ℓ + dfc lit σ Y ℓ) := by
  obtain ⟨c, hc⟩ := dfc_even lit σ hlit Y ℓ
  have hadd := fl_add lit Y ℓ
  have hle1 := fl_maj_le lit Y ℓ true
  have hle2 := fl_maj_le lit Y ℓ false
  by_cases hc0 : c = 0
  · have hd0 : dfc lit (Equiv.refl T) Y ℓ = 0 := by omega
    have hd1 : dfc lit σ Y ℓ = 0 := by omega
    unfold dfc at hd0 hd1
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hd0 hd1
    have := fl_zero_of lit σ hlit htr Y ℓ
      (fun t ht => by
        by_contra hne
        exact hd0 (Finset.mem_univ t) ⟨ht, hne⟩)
      (fun t ht => by
        by_contra hne
        exact hd1 (Finset.mem_univ t) ⟨ht, hne⟩)
    rw [this]
    exact Nat.zero_le _
  · rw [hc]
    have h2 : 2 ≤ c + c := by omega
    calc 2 * fl lit Y ℓ (maj lit Y ℓ) ≤ K * 2 := by omega
      _ ≤ K * (c + c) := Nat.mul_le_mul_left K h2

lemma round_bound {T L : Type} [Fintype T] [Fintype L] [DecidableEq L] (lit : T → L)
    (σ : Equiv.Perm T) (hlit : ∀ t, lit (σ t) = lit t)
    (htr : ∀ f : T → Bool, (∀ t, f (σ t) = f t) → ∀ t t', lit t = lit t' → f t = f t')
    (Y : Bool × T → Bool) (K : ℕ)
    (hK : ∀ ℓ, (Finset.univ.filter (fun t : T => lit t = ℓ)).card ≤ K) :
    2 * (Finset.univ.filter (fun u : Bool × T => Y u ≠ maj lit Y (lit u.2))).card ≤
      K * ((Finset.univ.filter (fun t : T => Y (false, t) ≠ Y (true, t))).card +
        (Finset.univ.filter (fun t : T => Y (false, t) ≠ Y (true, σ t))).card) := by
  have h1 : (Finset.univ.filter (fun u : Bool × T => Y u ≠ maj lit Y (lit u.2))).card =
      ∑ ℓ : L, fl lit Y ℓ (maj lit Y ℓ) := by
    rw [fib (fun u : Bool × T => lit u.2)]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    unfold fl
    congr 1
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h, h'⟩
      subst h
      exact ⟨rfl, h'⟩
    · rintro ⟨h, h'⟩
      subst h
      exact ⟨rfl, h'⟩
  have h2 : (Finset.univ.filter (fun t : T => Y (false, t) ≠ Y (true, t))).card =
      ∑ ℓ : L, dfc lit (Equiv.refl T) Y ℓ := by
    rw [fib lit]
    rfl
  have h3 : (Finset.univ.filter (fun t : T => Y (false, t) ≠ Y (true, σ t))).card =
      ∑ ℓ : L, dfc lit σ Y ℓ := by
    rw [fib lit]
    rfl
  rw [h1, h2, h3, ← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_le_sum fun ℓ _ => class_bound lit σ hlit htr Y ℓ K (hK ℓ)

def occF {v m : ℕ} (idx : Fin m → Fin 3 → Fin v) (sign : Fin m → Fin 3 → Bool) (i : Fin v)
    (s : Bool) : ℕ :=
  ((Finset.univ : Finset (Fin m × Fin 3)).filter (fun p =>
    idx p.1 p.2 = i ∧ sign p.1 p.2 = s)).card

def enc {v : ℕ} (x : Fin v → Bool) (ℓ : Bool × Fin v) : Bool := x ℓ.2 != ℓ.1

def dx {v : ℕ} (r : Fin v → Bool) (z : Bool × Fin v → Bool) (i : Fin v) : Bool :=
  if z (false, i) = z (true, i) ∧ r i = false then !z (false, i) else z (false, i)

def cutv {v m : ℕ} (idx : Fin m → Fin 3 → Fin v) (sign : Fin m → Fin 3 → Bool) (w : Fin v → ℕ)
    (z : Bool × Fin v → Bool) : ℕ :=
  2 * ∑ i : Fin v, w i * (if z (false, i) ≠ z (true, i) then 1 else 0) +
    2 * ∑ j : Fin m, ∑ a : Fin 3,
      (if z (sign j a, idx j a) ≠ z (sign j (a + 1), idx j (a + 1)) then 1 else 0)

lemma tri3 : ∀ f : Fin 3 → Bool, (∑ a : Fin 3, if f a ≠ f (a + 1) then 1 else 0) =
    if ∃ a b : Fin 3, f a ≠ f b then 2 else 0 := by
  decide

lemma enc_ne {v : ℕ} (x : Fin v → Bool) (i : Fin v) : enc x (false, i) ≠ enc x (true, i) := by
  unfold enc
  cases x i <;> simp

lemma cutv_enc {v m : ℕ} (idx : Fin m → Fin 3 → Fin v) (sign : Fin m → Fin 3 → Bool)
    (w : Fin v → ℕ) (x : Fin v → Bool) :
    cutv idx sign w (enc x) = 2 * ∑ i : Fin v, w i +
      4 * (Finset.univ.filter (fun j : Fin m => ∃ a b : Fin 3,
        (x (idx j a) != sign j a) ≠ (x (idx j b) != sign j b))).card := by
  unfold cutv
  have h1 : ∀ i : Fin v, w i * (if enc x (false, i) ≠ enc x (true, i) then 1 else 0) = w i := by
    intro i
    rw [if_pos (enc_ne x i), mul_one]
  have h2 : ∀ j : Fin m, (∑ a : Fin 3,
      (if enc x (sign j a, idx j a) ≠ enc x (sign j (a + 1), idx j (a + 1)) then 1 else 0)) =
      2 * (if ∃ a b : Fin 3, (x (idx j a) != sign j a) ≠ (x (idx j b) != sign j b)
        then 1 else 0) := by
    intro j
    have := tri3 (fun a => x (idx j a) != sign j a)
    rw [show (∑ a : Fin 3,
      (if enc x (sign j a, idx j a) ≠ enc x (sign j (a + 1), idx j (a + 1)) then 1 else 0)) =
      _ from this]
    split_ifs <;> rfl
  rw [Finset.sum_congr rfl (fun i _ => h1 i), Finset.sum_congr rfl (fun j _ => h2 j),
    ← Finset.mul_sum, Finset.card_filter]
  ring

lemma F_char {v : ℕ} (r : Fin v → Bool) (z : Bool × Fin v → Bool) (i : Fin v) (s : Bool) :
    (z (s, i) ≠ enc (dx r z) (s, i)) ↔ (z (false, i) = z (true, i) ∧ s = r i) := by
  unfold enc dx
  cases s <;> cases h1 : z (false, i) <;> cases h2 : z (true, i) <;> cases h3 : r i <;> simp

lemma dx_enc {v : ℕ} (r : Fin v → Bool) (x : Fin v → Bool) : dx r (enc x) = x := by
  funext i
  unfold dx enc
  cases x i <;> cases r i <;> simp

lemma repair {v m : ℕ} (idx : Fin m → Fin 3 → Fin v) (sign : Fin m → Fin 3 → Bool)
    (w : Fin v → ℕ) (r : Fin v → Bool) (z : Bool × Fin v → Bool)
    (hw : ∀ i, 1 + 2 * occF idx sign i (r i) ≤ w i) :
    cutv idx sign w z +
        2 * (Finset.univ.filter (fun i : Fin v => z (false, i) = z (true, i))).card ≤
      cutv idx sign w (enc (dx r z)) := by
  have hF : (∑ j : Fin m, ∑ a : Fin 3,
      (if z (sign j a, idx j a) ≠ enc (dx r z) (sign j a, idx j a) then 1 else 0)) =
      ∑ i : Fin v, if z (false, i) = z (true, i) then occF idx sign i (r i) else 0 := by
    rw [← Fintype.sum_prod_type (f := fun p : Fin m × Fin 3 =>
      if z (sign p.1 p.2, idx p.1 p.2) ≠ enc (dx r z) (sign p.1 p.2, idx p.1 p.2) then 1 else 0),
      ← Finset.card_filter, fib (fun p : Fin m × Fin 3 => idx p.1 p.2)]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs with h
    · unfold occF
      congr 1
      ext p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hi, hne⟩
        rw [F_char, hi] at hne
        exact ⟨hi, hne.2⟩
      · rintro ⟨hi, hs⟩
        refine ⟨hi, ?_⟩
        rw [F_char, hi]
        exact ⟨h, hs⟩
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro p - ⟨hi, hne⟩
      rw [F_char, hi] at hne
      exact h hne.1
  have hj : ∀ j : Fin m, (∑ a : Fin 3,
      (if z (sign j a, idx j a) ≠ z (sign j (a + 1), idx j (a + 1)) then 1 else 0)) ≤
      (∑ a : Fin 3, (if enc (dx r z) (sign j a, idx j a) ≠
        enc (dx r z) (sign j (a + 1), idx j (a + 1)) then 1 else 0)) +
      2 * ∑ a : Fin 3,
        (if z (sign j a, idx j a) ≠ enc (dx r z) (sign j a, idx j a) then 1 else 0) := by
    intro j
    have hs : (∑ a : Fin 3, (if z (sign j (a + 1), idx j (a + 1)) ≠
        enc (dx r z) (sign j (a + 1), idx j (a + 1)) then 1 else 0)) =
        ∑ a : Fin 3,
          (if z (sign j a, idx j a) ≠ enc (dx r z) (sign j a, idx j a) then 1 else 0) :=
      Equiv.sum_comp (Equiv.addRight (1 : Fin 3)) (fun a : Fin 3 =>
        if z (sign j a, idx j a) ≠ enc (dx r z) (sign j a, idx j a) then 1 else 0)
    rw [two_mul]
    nth_rewrite 2 [← hs]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun a _ => ?_
    have := b4 (z (sign j a, idx j a)) (z (sign j (a + 1), idx j (a + 1)))
      (enc (dx r z) (sign j a, idx j a)) (enc (dx r z) (sign j (a + 1), idx j (a + 1)))
    omega
  have hA := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin m))) => hj j)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, hF] at hA
  have hP : (∑ i : Fin v, w i * (if z (false, i) ≠ z (true, i) then 1 else 0)) +
      2 * (∑ i : Fin v, if z (false, i) = z (true, i) then occF idx sign i (r i) else 0) +
      (Finset.univ.filter (fun i : Fin v => z (false, i) = z (true, i))).card ≤
      ∑ i : Fin v, w i * (if enc (dx r z) (false, i) ≠ enc (dx r z) (true, i) then 1 else 0) := by
    rw [Finset.card_filter, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [if_pos (enc_ne _ i)]
    have := hw i
    by_cases h : z (false, i) = z (true, i)
    · simp only [h, ne_eq, not_true_eq_false, ite_false, ite_true]
      omega
    · simp only [h, ne_eq, not_false_eq_true, ite_false, ite_true]
      omega
  unfold cutv
  omega

lemma dist2 {T : Type} [Fintype T] {v : ℕ} (lit : T → Bool × Fin v) (r : Fin v → Bool)
    (z : Bool × Fin v → Bool) (K : ℕ)
    (hK : ∀ ℓ, (Finset.univ.filter (fun t : T => lit t = ℓ)).card ≤ K) :
    (Finset.univ.filter (fun t : T => z (lit t) ≠ enc (dx r z) (lit t))).card ≤
      K * (Finset.univ.filter (fun i : Fin v => z (false, i) = z (true, i))).card := by
  have hterm : ∀ (s : Bool) (i : Fin v),
      (Finset.univ.filter (fun t : T => lit t = (s, i) ∧
        z (lit t) ≠ enc (dx r z) (lit t))).card ≤
        if z (false, i) = z (true, i) ∧ s = r i then K else 0 := by
    intro s i
    split_ifs with h
    · refine le_trans (Finset.card_le_card ?_) (hK (s, i))
      intro t ht
      rw [Finset.mem_filter] at ht ⊢
      exact ⟨ht.1, ht.2.1⟩
    · rw [Nat.le_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro t - ⟨hl, hne⟩
      rw [hl] at hne
      exact h ((F_char r z i s).mp hne)
  rw [fib lit, Fintype.sum_prod_type, Finset.sum_comm, Finset.card_filter, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Fintype.sum_bool]
  have ht := hterm true i
  have hf := hterm false i
  by_cases hE : z (false, i) = z (true, i) <;> cases hr : r i <;>
    simp only [hE, hr, true_and, false_and, and_true, and_false, reduceCtorEq,
      ↓reduceIte, mul_one, mul_zero] at ht hf ⊢ <;> omega

lemma core_ineq {T : Type} [Fintype T] {v m : ℕ} (B : ℕ) (idx : Fin m → Fin 3 → Fin v)
    (sign : Fin m → Fin 3 → Bool) (w : Fin v → ℕ) (r : Fin v → Bool)
    (lit : T → Bool × Fin v) (σ μ : Equiv.Perm T)
    (hσ : ∀ t, lit (σ t) = lit t)
    (htr : ∀ f : T → Bool, (∀ t, f (σ t) = f t) → ∀ t t', lit t = lit t' → f t = f t')
    (hNB : ∀ ℓ, (Finset.univ.filter (fun t : T => lit t = ℓ)).card ≤ 2 * B + 1)
    (hcut : ∀ z : Bool × Fin v → Bool,
      (Finset.univ.filter (fun t : T => z (lit t) ≠ z (lit (μ t)))).card = cutv idx sign w z)
    (hw : ∀ i, 1 + 2 * occF idx sign i (r i) ≤ w i) (Y : Bool × T → Bool) :
    (Finset.univ.filter (fun u : Bool × T => Y u ≠ enc (dx r (maj lit Y)) (lit u.2))).card +
        (2 * B + 1) * (Finset.univ.filter (fun t : T => Y (false, t) ≠ Y (true, μ t))).card ≤
      (2 * B + 1) * (cutv idx sign w (enc (dx r (maj lit Y))) +
        (B + 1) * ((Finset.univ.filter (fun t : T => Y (false, t) ≠ Y (true, t))).card +
          (Finset.univ.filter (fun t : T => Y (false, t) ≠ Y (true, σ t))).card)) := by
  have h1 := round_bound lit σ hσ htr Y (2 * B + 1) hNB
  have h2 := lips μ Y (fun u => maj lit Y (lit u.2))
  have h3 := hcut (maj lit Y)
  have h4 := repair idx sign w r (maj lit Y) hw
  have h5 := dist2 lit r (maj lit Y) (2 * B + 1) hNB
  have h6 := tri_ineq Y (fun u : Bool × T => maj lit Y (lit u.2))
    (fun u : Bool × T => enc (dx r (maj lit Y)) (lit u.2))
  have h7 := dbl (fun t : T => maj lit Y (lit t) ≠ enc (dx r (maj lit Y)) (lit t))
  simp only at h2 h6 h7
  rw [h3] at h2
  rw [h7] at h6
  have e2 := Nat.mul_le_mul_left (2 * B + 1) h2
  have e4 := Nat.mul_le_mul_left (2 * B + 1) h4
  have e1 := Nat.mul_le_mul_left (B + 1) h1
  nlinarith

def glit {v m : ℕ} (idx : Fin m → Fin 3 → Fin v) (sign : Fin m → Fin 3 → Bool)
    (w g : Fin v → ℕ) (r : Fin v → Bool) :
    (Fin m × Fin 3 × Bool) ⊕ (Σ i : Fin v, (Bool × Fin (w i)) ⊕ Fin (g i)) → Bool × Fin v :=
  Sum.elim (fun p => (sign p.1 p.2.1, idx p.1 p.2.1))
    (fun q => Sum.elim (fun sk => (sk.1, q.1)) (fun _ => (r q.1, q.1)) q.2)

def gmu (v m : ℕ) (w g : Fin v → ℕ) :
    Equiv.Perm ((Fin m × Fin 3 × Bool) ⊕ (Σ i : Fin v, (Bool × Fin (w i)) ⊕ Fin (g i))) :=
  Equiv.sumCongr
    (Equiv.prodCongr (Equiv.refl _) (Equiv.prodCongr (Equiv.addRight 1) (Equiv.refl _)))
    (Equiv.sigmaCongrRight fun i =>
      Equiv.sumCongr (Equiv.prodCongr Equiv.boolNot (Equiv.refl _)) (Equiv.refl _))

lemma gcut {v m : ℕ} (idx : Fin m → Fin 3 → Fin v) (sign : Fin m → Fin 3 → Bool)
    (w g : Fin v → ℕ) (r : Fin v → Bool) (z : Bool × Fin v → Bool) :
    (Finset.univ.filter (fun t => z (glit idx sign w g r t) ≠
      z (glit idx sign w g r (gmu v m w g t)))).card = cutv idx sign w z := by
  rw [Finset.card_filter, Fintype.sum_sum_type, Fintype.sum_sigma, add_comm]
  unfold cutv
  congr 1
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_bool]
    have e1 : ∀ k : Fin (w i), (if z (glit idx sign w g r (Sum.inr ⟨i, Sum.inl (true, k)⟩)) ≠
        z (glit idx sign w g r (gmu v m w g (Sum.inr ⟨i, Sum.inl (true, k)⟩))) then 1 else 0) =
        if z (false, i) ≠ z (true, i) then 1 else 0 := by
      intro k
      show (if z (true, i) ≠ z (false, i) then 1 else 0) = _
      by_cases h : z (false, i) = z (true, i)
      · rw [if_neg (not_not.mpr h), if_neg (not_not.mpr h.symm)]
      · rw [if_pos h, if_pos (Ne.symm h)]
    have e2 : ∀ k : Fin (w i), (if z (glit idx sign w g r (Sum.inr ⟨i, Sum.inl (false, k)⟩)) ≠
        z (glit idx sign w g r (gmu v m w g (Sum.inr ⟨i, Sum.inl (false, k)⟩))) then 1 else 0) =
        if z (false, i) ≠ z (true, i) then 1 else 0 := fun k => rfl
    have e3 : ∀ k : Fin (g i), (if z (glit idx sign w g r (Sum.inr ⟨i, Sum.inr k⟩)) ≠
        z (glit idx sign w g r (gmu v m w g (Sum.inr ⟨i, Sum.inr k⟩))) then 1 else 0) = 0 := by
      intro k
      exact if_neg (not_not.mpr rfl)
    rw [Finset.sum_congr rfl (fun k _ => e1 k), Finset.sum_congr rfl (fun k _ => e2 k),
      Finset.sum_congr rfl (fun k _ => e3 k), Finset.sum_const, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin]
    simp only [smul_eq_mul, mul_zero, add_zero]
    ring
  · rw [Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Fintype.sum_bool, two_mul]
    rfl

lemma gN {v m : ℕ} (idx : Fin m → Fin 3 → Fin v) (sign : Fin m → Fin 3 → Bool)
    (w g : Fin v → ℕ) (r : Fin v → Bool) (s : Bool) (i : Fin v) :
    (Finset.univ.filter (fun t => glit idx sign w g r t = (s, i))).card =
      2 * occF idx sign i s + w i + (if r i = s then g i else 0) := by
  rw [Finset.card_filter, Fintype.sum_sum_type, Fintype.sum_sigma, add_assoc]
  congr 1
  · unfold occF
    rw [Finset.card_filter, Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Fintype.sum_bool, two_mul]
    have : (glit idx sign w g r (Sum.inl (j, a, true)) = (s, i)) ↔
        (idx j a = i ∧ sign j a = s) := by
      show (sign j a, idx j a) = (s, i) ↔ _
      rw [Prod.mk.injEq, and_comm]
    have h2 : (glit idx sign w g r (Sum.inl (j, a, false)) = (s, i)) ↔
        (idx j a = i ∧ sign j a = s) := this
    simp only [this, h2]
  · have hi : ∀ i' : Fin v, (∑ y : (Bool × Fin (w i')) ⊕ Fin (g i'),
        (if glit idx sign w g r (Sum.inr ⟨i', y⟩) = (s, i) then 1 else 0)) =
        if i' = i then (w i + (if r i = s then g i else 0)) else 0 := by
      intro i'
      rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
      have e1 : ∀ (s' : Bool) (k : Fin (w i')),
          (glit idx sign w g r (Sum.inr ⟨i', Sum.inl (s', k)⟩) = (s, i)) ↔ (s' = s ∧ i' = i) := by
        intro s' k
        show (s', i') = (s, i) ↔ _
        rw [Prod.mk.injEq]
      have e2 : ∀ (k : Fin (g i')),
          (glit idx sign w g r (Sum.inr ⟨i', Sum.inr k⟩) = (s, i)) ↔ (r i' = s ∧ i' = i) := by
        intro k
        show (r i', i') = (s, i) ↔ _
        rw [Prod.mk.injEq]
      simp only [e1, e2]
      by_cases h : i' = i
      · subst h
        cases s <;> simp
      · simp [h]
    rw [Finset.sum_congr rfl (fun i' _ => hi i'), Finset.sum_ite_eq' Finset.univ i]
    simp

lemma occ_sum {v m : ℕ} (idx : Fin m → Fin 3 → Fin v) (sign : Fin m → Fin 3 → Bool) :
    ∑ i : Fin v, (occF idx sign i false + occF idx sign i true) = 3 * m := by
  have h1 : ∀ i : Fin v, occF idx sign i false + occF idx sign i true =
      (Finset.univ.filter (fun p : Fin m × Fin 3 => idx p.1 p.2 = i ∧ True)).card := by
    intro i
    unfold occF
    rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases h : idx p.1 p.2 = i <;> cases sign p.1 p.2 <;> simp [h]
  rw [Finset.sum_congr rfl (fun i _ => h1 i),
    ← fib (fun p : Fin m × Fin 3 => idx p.1 p.2) (fun _ => True)]
  simp [mul_comm]

lemma gcard {v m : ℕ} (idx : Fin m → Fin 3 → Fin v) (sign : Fin m → Fin 3 → Bool) :
    Fintype.card ((Fin m × Fin 3 × Bool) ⊕ (Σ i : Fin v,
      (Bool × Fin (1 + 2 * min (occF idx sign i false) (occF idx sign i true))) ⊕
        Fin (2 * (max (occF idx sign i false) (occF idx sign i true) -
          min (occF idx sign i false) (occF idx sign i true))))) = 2 * (v + 6 * m) := by
  have h := occ_sum idx sign
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_sigma, Fintype.card_fin,
    Fintype.card_bool]
  have h2 : ∀ i : Fin v, 2 * (1 + 2 * min (occF idx sign i false) (occF idx sign i true)) +
      2 * (max (occF idx sign i false) (occF idx sign i true) -
          min (occF idx sign i false) (occF idx sign i true)) =
      2 + 2 * (occF idx sign i false + occF idx sign i true) := by
    intro i
    omega
  rw [Finset.sum_congr rfl (fun i _ => h2 i), Finset.sum_add_distrib, ← Finset.mul_sum, h]
  simp
  omega

lemma tr1 {T : Type} [Fintype T] {n : ℕ} (e : T ≃ Fin n) (P : Fin n → Prop) [DecidablePred P] :
    (Finset.univ.filter P).card = (Finset.univ.filter (fun t : T => P (e t))).card := by
  rw [Finset.card_filter, Finset.card_filter]
  exact (Equiv.sum_comp e _).symm

lemma tr2 {T : Type} [Fintype T] {n : ℕ} (e : T ≃ Fin n) (P : Bool × Fin n → Prop)
    [DecidablePred P] :
    (Finset.univ.filter P).card =
      (Finset.univ.filter (fun u : Bool × T => P (u.1, e u.2))).card := by
  rw [Finset.card_filter, Finset.card_filter]
  exact (Equiv.sum_comp ((Equiv.refl Bool).prodCongr e) _).symm

lemma maj_enc {T : Type} [Fintype T] {v : ℕ} (lit : T → Bool × Fin v)
    (hpos : ∀ ℓ, 0 < (Finset.univ.filter (fun t : T => lit t = ℓ)).card) (x : Fin v → Bool) :
    maj lit (fun u : Bool × T => enc x (lit u.2)) = enc x := by
  funext ℓ
  have h0 : fl lit (fun u : Bool × T => enc x (lit u.2)) ℓ (enc x ℓ) = 0 := by
    unfold fl
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro u - ⟨hl, hne⟩
    exact hne (by
      show enc x (lit u.2) = enc x ℓ
      rw [hl])
  have hadd := fl_add lit (fun u : Bool × T => enc x (lit u.2)) ℓ
  have hp := hpos ℓ
  unfold maj
  cases hx : enc x ℓ
  · rw [hx] at h0
    rw [decide_eq_false_iff_not]
    omega
  · rw [hx] at h0
    rw [decide_eq_true_eq]
    omega

lemma cnt_true {T : Type} [Fintype T] {v : ℕ} (lit : T → Bool × Fin v) (c : Fin v → ℕ)
    (hN : ∀ ℓ, (Finset.univ.filter (fun t : T => lit t = ℓ)).card = c ℓ.2) (x : Fin v → Bool) :
    (Finset.univ.filter (fun u : Bool × T => enc x (lit u.2) = true)).card =
      2 * ∑ i : Fin v, c i := by
  rw [dbl (fun t : T => enc x (lit t) = true), fib lit, Fintype.sum_prod_type, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_bool]
  have key : ∀ s : Bool, (Finset.univ.filter (fun t : T => lit t = (s, i) ∧
      enc x (lit t) = true)).card = if enc x (s, i) = true then c i else 0 := by
    intro s
    split_ifs with h
    · rw [← hN (s, i)]
      congr 1
      ext t
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact fun h' => h'.1
      · intro h'
        exact ⟨h', by rw [h']; exact h⟩
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro t - ⟨hl, ht⟩
      rw [hl] at ht
      exact h ht
  rw [key true, key false]
  unfold enc
  cases x i <;> simp

lemma main : (∀ (v m B : ℕ) (idx : Fin m → Fin 3 → Fin v) (sign : Fin m → Fin 3 → Bool),
  let occ := fun (i : Fin v) (s : Bool) =>
    ((Finset.univ : Finset (Fin m × Fin 3)).filter (fun p =>
      idx p.1 p.2 = i ∧ sign p.1 p.2 = s)).card
  (∀ i, occ i false + occ i true ≤ B) →
  let R := ∑ i : Fin v, (1+2*min (occ i false) (occ i true))
  let sat := fun x : Fin v → Bool =>
    (Finset.univ.filter (fun j : Fin m => ∃ a b : Fin 3,
      (x (idx j a) != sign j a) ≠ (x (idx j b) != sign j b))).card
  let n := 2*(v+6*m)
  let V := Bool × Fin n
  let X := V → Bool
  ∃ (M : Fin 3 → Equiv.Perm (Fin n)) (label : V → Bool × Fin v)
    (decode : X → (Fin v → Bool)),
    let cost := fun (y : X) (j : Fin 3) =>
      (Finset.univ.filter (fun i : Fin n => y (false,i) ≠ y (true,M j i))).card
    let encode := fun (x : Fin v → Bool) (u : V) => x (label u).2 != (label u).1
    (∀ x : Fin v → Bool, decode (encode x) = x ∧
      (Finset.univ.filter (fun u : V => encode x u = true)).card = n ∧
      cost (encode x) 0 = 0 ∧ cost (encode x) 1 = 0 ∧ cost (encode x) 2 = 2*R + 4*sat x) ∧
    ∀ y : X,
      (Finset.univ.filter (fun u : V => y u ≠ encode (decode y) u)).card + (2*B+1)*cost y 2 ≤
        (2*B+1)*(2*R + 4*sat (decode y) + (B+1)*(cost y 0 + cost y 1))) := by
  intro v m B idx sign occ hB R sat n V X
  have hB' : ∀ i, occF idx sign i false + occF idx sign i true ≤ B := hB
  obtain ⟨σ, hσ, htr⟩ := exists_cyc (glit idx sign
    (fun i => 1 + 2 * min (occF idx sign i false) (occF idx sign i true))
    (fun i => 2 * (max (occF idx sign i false) (occF idx sign i true) -
          min (occF idx sign i false) (occF idx sign i true)))
    (fun i => decide (occF idx sign i true < occF idx sign i false)))
  have hN : ∀ ℓ : Bool × Fin v, (Finset.univ.filter (fun t => glit idx sign
      (fun i => 1 + 2 * min (occF idx sign i false) (occF idx sign i true))
      (fun i => 2 * (max (occF idx sign i false) (occF idx sign i true) -
          min (occF idx sign i false) (occF idx sign i true)))
      (fun i => decide (occF idx sign i true < occF idx sign i false)) t = ℓ)).card =
      1 + 2 * (occF idx sign ℓ.2 false + occF idx sign ℓ.2 true) := by
    rintro ⟨s, i⟩
    rw [gN]
    by_cases h : occF idx sign i true < occF idx sign i false <;> cases s <;> simp [h] <;> omega
  have hw : ∀ i : Fin v, 1 + 2 * occF idx sign i
      (decide (occF idx sign i true < occF idx sign i false)) ≤
      1 + 2 * min (occF idx sign i false) (occF idx sign i true) := by
    intro i
    by_cases h : occF idx sign i true < occF idx sign i false <;> simp [h] <;> omega
  have hsum := occ_sum idx sign
  have hcut := gcut idx sign
    (fun i => 1 + 2 * min (occF idx sign i false) (occF idx sign i true))
    (fun i => 2 * (max (occF idx sign i false) (occF idx sign i true) -
          min (occF idx sign i false) (occF idx sign i true)))
    (fun i => decide (occF idx sign i true < occF idx sign i false))
  generalize hlit : glit idx sign
    (fun i => 1 + 2 * min (occF idx sign i false) (occF idx sign i true))
    (fun i => 2 * (max (occF idx sign i false) (occF idx sign i true) -
          min (occF idx sign i false) (occF idx sign i true)))
    (fun i => decide (occF idx sign i true < occF idx sign i false)) = lit at hσ htr hN hcut
  generalize gmu v m
    (fun i => 1 + 2 * min (occF idx sign i false) (occF idx sign i true))
    (fun i => 2 * (max (occF idx sign i false) (occF idx sign i true) -
          min (occF idx sign i false) (occF idx sign i true))) = μ at hcut
  have e := Fintype.equivFinOfCardEq (gcard idx sign)
  have hNB : ∀ ℓ, (Finset.univ.filter (fun t => lit t = ℓ)).card ≤ 2 * B + 1 := by
    intro ℓ
    rw [hN]
    have := hB' ℓ.2
    omega
  have hpos : ∀ ℓ, 0 < (Finset.univ.filter (fun t => lit t = ℓ)).card := by
    intro ℓ
    rw [hN]
    omega
  refine ⟨fun j => e.symm.trans ((![Equiv.refl _, σ, μ] j).trans e),
    fun u => lit (e.symm u.2),
    fun y => dx (fun i => decide (occF idx sign i true < occF idx sign i false))
      (maj lit (fun u => y (u.1, e u.2))), ?_⟩
  intro cost encode
  have hcost : ∀ (y : X) (j : Fin 3), cost y j = (Finset.univ.filter (fun t =>
      y (false, e t) ≠ y (true, e ((![Equiv.refl _, σ, μ] j) t)))).card := by
    intro y j
    show (Finset.univ.filter (fun i : Fin n => y (false, i) ≠
      y (true, e ((![Equiv.refl _, σ, μ] j) (e.symm i))))).card = _
    rw [tr1 e]
    simp only [Equiv.symm_apply_apply]
  have henc : ∀ (x : Fin v → Bool), (fun u : Bool × _ => encode x (u.1, e u.2)) =
      fun u : Bool × _ => enc x (lit u.2) := by
    intro x
    funext u
    show enc x (lit (e.symm (e u.2))) = _
    rw [Equiv.symm_apply_apply]
  have hR : 2 * ∑ i : Fin v, (1 + 2 * min (occF idx sign i false) (occF idx sign i true)) = 2 * R :=
    rfl
  refine ⟨fun x => ⟨?_, ?_, ?_, ?_, ?_⟩, fun y => ?_⟩
  · show dx _ (maj lit (fun u => encode x (u.1, e u.2))) = x
    rw [henc, maj_enc lit hpos, dx_enc]
  · rw [tr2 e]
    trans (Finset.univ.filter (fun u : Bool × _ => enc x (lit u.2) = true)).card
    · congr 1
      ext u
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      show enc x (lit (e.symm (e u.2))) = true ↔ _
      rw [Equiv.symm_apply_apply]
    rw [cnt_true lit (fun i => 1 + 2 * (occF idx sign i false + occF idx sign i true))
      (fun ℓ => hN ℓ), Finset.sum_add_distrib, ← Finset.mul_sum, hsum]
    simp
    omega
  · rw [hcost, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro t _ h
    exact h (by
      show enc x (lit (e.symm (e t))) = enc x (lit (e.symm (e t)))
      rfl)
  · rw [hcost, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro t _ h
    apply h
    show enc x (lit (e.symm (e t))) = enc x (lit (e.symm (e (σ t))))
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply, hσ]
  · rw [hcost]
    have := hcut (enc x)
    rw [cutv_enc, hR] at this
    rw [← this]
    congr 1
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    show (enc x (lit (e.symm (e t))) ≠ enc x (lit (e.symm (e (μ t))))) ↔ _
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  · have key := core_ineq B idx sign _ _ lit σ μ hσ htr hNB hcut hw (fun u => y (u.1, e u.2))
    rw [cutv_enc, hR] at key
    have hc0 : cost y 0 = (Finset.univ.filter (fun t =>
        y (false, e t) ≠ y (true, e t))).card := hcost y 0
    have hc1 : cost y 1 = (Finset.univ.filter (fun t =>
        y (false, e t) ≠ y (true, e (σ t)))).card := hcost y 1
    have hc2 : cost y 2 = (Finset.univ.filter (fun t =>
        y (false, e t) ≠ y (true, e (μ t)))).card := hcost y 2
    rw [hc0, hc1, hc2, tr2 e]
    refine le_trans (le_of_eq ?_) key
    congr 2
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    show (y (u.1, e u.2) ≠ enc _ (lit (e.symm (e u.2)))) ↔ _
    rw [Equiv.symm_apply_apply]

end PEqualNP.Outside.L_pcx_368

theorem PEqualNP.Outside.L_pcx_368 : (∀ (v m B : ℕ) (idx : Fin m → Fin 3 → Fin v) (sign : Fin m → Fin 3 → Bool),
  let occ := fun (i : Fin v) (s : Bool) =>
    ((Finset.univ : Finset (Fin m × Fin 3)).filter (fun p =>
      idx p.1 p.2 = i ∧ sign p.1 p.2 = s)).card
  (∀ i, occ i false + occ i true ≤ B) →
  let R := ∑ i : Fin v, (1+2*min (occ i false) (occ i true))
  let sat := fun x : Fin v → Bool =>
    (Finset.univ.filter (fun j : Fin m => ∃ a b : Fin 3,
      (x (idx j a) != sign j a) ≠ (x (idx j b) != sign j b))).card
  let n := 2*(v+6*m)
  let V := Bool × Fin n
  let X := V → Bool
  ∃ (M : Fin 3 → Equiv.Perm (Fin n)) (label : V → Bool × Fin v)
    (decode : X → (Fin v → Bool)),
    let cost := fun (y : X) (j : Fin 3) =>
      (Finset.univ.filter (fun i : Fin n => y (false,i) ≠ y (true,M j i))).card
    let encode := fun (x : Fin v → Bool) (u : V) => x (label u).2 != (label u).1
    (∀ x : Fin v → Bool, decode (encode x) = x ∧
      (Finset.univ.filter (fun u : V => encode x u = true)).card = n ∧
      cost (encode x) 0 = 0 ∧ cost (encode x) 1 = 0 ∧ cost (encode x) 2 = 2*R + 4*sat x) ∧
    ∀ y : X,
      (Finset.univ.filter (fun u : V => y u ≠ encode (decode y) u)).card + (2*B+1)*cost y 2 ≤
        (2*B+1)*(2*R + 4*sat (decode y) + (B+1)*(cost y 0 + cost y 1))) := by
  exact PEqualNP.Outside.L_pcx_368.main
