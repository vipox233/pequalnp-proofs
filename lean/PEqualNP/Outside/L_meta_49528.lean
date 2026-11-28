import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_49528

open Matrix

def Grid {V J : Type} [Preorder V] (P Z : V → J → Prop) (D B : ℕ) : Prop :=
  ∃ f : V → J → ℕ,
    (∀ x j, f x j ≤ D) ∧ (∀ x j, P x j → f x j = D) ∧
    (∀ x j, Z x j → f x j = 0) ∧ (∀ x y, x ≤ y → ∀ j, f y j ≤ f x j) ∧
    ∀ (l : ℕ) (p : Fin (l+1) → V) (a : Fin l → J),
      (∀ i : Fin l, p i.castSucc ≤ p i.succ) →
      ∑ i : Fin l, (f (p i.castSucc) (a i) - f (p i.succ) (a i)) ≤ B

lemma grid_zero {V J : Type} [Preorder V] (P Z : V → J → Prop) : Grid P Z 0 0 := by
  refine ⟨fun _ _ => 0, by simp, by simp, by simp, by simp, ?_⟩
  simp

lemma grid_mono {V J : Type} [Preorder V] {P Z : V → J → Prop} {D B E : ℕ}
    (h : Grid P Z D B) (he : B ≤ E) : Grid P Z D E := by
  obtain ⟨f, hD, hP, hZ, ha, hc⟩ := h
  exact ⟨f, hD, hP, hZ, ha, fun l p a hp => (hc l p a hp).trans he⟩

lemma grid_add {V J : Type} [Preorder V] {P Z : V → J → Prop} {D B E F : ℕ}
    (h : Grid P Z D B) (k : Grid P Z E F) : Grid P Z (D+E) (B+F) := by
  obtain ⟨f, fD, fP, fZ, fa, fc⟩ := h
  obtain ⟨g, gE, gP, gZ, ga, gc⟩ := k
  refine ⟨fun x j => f x j + g x j, fun x j => Nat.add_le_add (fD x j) (gE x j),
    fun x j hx => by simp [fP x j hx, gP x j hx],
    fun x j hx => by simp [fZ x j hx, gZ x j hx],
    fun x y hxy j => Nat.add_le_add (fa x y hxy j) (ga x y hxy j), ?_⟩
  intro l p a hp
  calc ∑ i : Fin l, (f (p i.castSucc) (a i) + g (p i.castSucc) (a i) -
          (f (p i.succ) (a i) + g (p i.succ) (a i))) =
        ∑ i : Fin l, ((f (p i.castSucc) (a i) - f (p i.succ) (a i)) +
          (g (p i.castSucc) (a i) - g (p i.succ) (a i))) := by
            apply Finset.sum_congr rfl
            intro i _
            have := fa _ _ (hp i) (a i)
            have := ga _ _ (hp i) (a i)
            omega
    _ ≤ B + F := by rw [Finset.sum_add_distrib]; exact Nat.add_le_add (fc l p a hp) (gc l p a hp)

lemma sum_telescope_int {l : ℕ} (g : Fin (l + 1) → ℤ) :
    Finset.univ.sum (fun i : Fin l => g i.castSucc - g i.succ) = g 0 - g (Fin.last l) := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [Fin.sum_univ_castSucc]
    have hih := ih (fun k => g k.castSucc)
    simp only [Fin.castSucc_zero] at hih
    have h1 : (∑ i : Fin l, (g i.castSucc.castSucc - g i.castSucc.succ)) = g 0 - g (Fin.last l).castSucc := by
      convert hih using 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Fin.succ_castSucc]
    rw [h1, Fin.succ_last]
    ring

lemma sum_telescope_nat_mono {l : ℕ} (g : Fin (l + 1) → ℕ)
    (hmono : ∀ i : Fin l, g i.castSucc ≤ g i.succ) :
    Finset.univ.sum (fun i : Fin l => g i.succ - g i.castSucc) = g (Fin.last l) - g 0 := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [Fin.sum_univ_castSucc]
    have hmono' : ∀ i : Fin l, g i.castSucc.castSucc ≤ g i.succ.castSucc := fun i => by
      rw [← Fin.succ_castSucc]
      exact hmono i.castSucc
    have hih := ih (fun k => g k.castSucc) hmono'
    simp only [Fin.castSucc_zero] at hih
    have h1 : (∑ i : Fin l, (g i.castSucc.succ - g i.castSucc.castSucc)) = g (Fin.last l).castSucc - g 0 := by
      convert hih using 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Fin.succ_castSucc]
    rw [h1]
    have h0_le : g 0 ≤ g (Fin.last l).castSucc := by
      have hgen : ∀ k : Fin (l + 1), g 0 ≤ g k.castSucc := by
        intro k
        induction k using Fin.induction with
        | zero => simp
        | succ k ihk => exact ihk.trans (hmono k.castSucc)
      exact hgen (Fin.last l)
    have hlast_le : g (Fin.last l).castSucc ≤ g (Fin.last l.succ) := by
      have := hmono (Fin.last l)
      rwa [Fin.succ_last] at this
    rw [Fin.succ_last]
    change g (Fin.last l).castSucc - g 0 + (g (Fin.last l.succ) - g (Fin.last l).castSucc) = g (Fin.last l.succ) - g 0
    omega

lemma height_exists (A : ℕ → ℕ → Prop) (hn : ∀ D, ∃ B, A D B)
    (hm : ∀ D B E, A D B → B ≤ E → A D E) (hz : A 0 0)
    (ha : ∀ D B E F, A D B → A E F → A (D+E) (B+F)) :
    ∃ H : ℕ → ℕ, (∀ D B, A D B ↔ H D ≤ B) ∧ H 0 = 0 ∧
      ∀ u v, H (u+v) ≤ H u + H v := by
  classical
  let H : ℕ → ℕ := fun D => Nat.find (hn D)
  have hf (D : ℕ) : A D (H D) := Nat.find_spec (hn D)
  have hc (D B : ℕ) : A D B ↔ H D ≤ B :=
    ⟨fun h => Nat.find_min' _ h, hm D _ B (hf D)⟩
  exact ⟨H, hc, Nat.eq_zero_of_le_zero ((hc 0 0).1 hz),
    fun u v => (hc _ _).1 (ha _ _ _ _ (hf u) (hf v))⟩

lemma semigroup_tail (H : ℕ → ℕ) (hz : H 0 = 0)
    (ha : ∀ u v, H (u+v) ≤ H u + H v) (q : ℕ) (hq : 0 < q)
    (hs : ∀ D, D * H q ≤ q * H D) :
    (∀ k, H (k*q) = k*H q) ∧ ∃ T : ℕ, ∀ D, T ≤ D → H (D+q) = H D + H q := by
  classical
  constructor
  · intro k
    apply le_antisymm
    · induction k with
      | zero => simpa using hz.le
      | succ k ih =>
        rw [Nat.succ_mul, Nat.succ_mul]
        exact (ha _ _).trans (Nat.add_le_add_right ih _)
    · apply Nat.le_of_mul_le_mul_left (c := q) _ hq
      calc q * (k * H q) = (k*q) * H q := by ring
        _ ≤ q * H (k*q) := hs _
  · let e : ℕ → ℕ := fun d => q * H d - d * H q
    have drop (d : ℕ) : e (d+q) ≤ e d := by
      have hx := Nat.mul_le_mul_left q (ha d q)
      rw [Nat.mul_add] at hx
      dsimp only [e]
      rw [Nat.add_mul]
      omega
    have mono (r : Fin q) : Antitone (fun k : ℕ => e (r.val + k*q)) := by
      apply antitone_nat_of_succ_le
      intro k
      simpa only [Nat.succ_mul, Nat.add_assoc] using drop (r.val + k*q)
    have ex (r : Fin q) : ∃ k : ℕ, ∀ j : ℕ, e (r.val + k*q) ≤ e (r.val + j*q) := by
      let s := Set.range (fun j : ℕ => e (r.val + j*q))
      have hn : s.Nonempty := ⟨_, ⟨0, rfl⟩⟩
      obtain ⟨k, hk⟩ := Nat.sInf_mem hn
      exact ⟨k, fun j => le_trans hk.le (Nat.sInf_le (s := s) ⟨j, rfl⟩)⟩
    choose K hK using ex
    let m := Finset.univ.sup K
    refine ⟨m*q, ?_⟩
    intro D hD
    let r : Fin q := ⟨D % q, Nat.mod_lt D hq⟩
    let k := D / q
    have he : r.val + k*q = D := by simpa [r, k, Nat.mul_comm] using Nat.mod_add_div D q
    have hk : K r ≤ k := (Finset.le_sup (f := K) (Finset.mem_univ r)).trans
      ((Nat.le_div_iff_mul_le hq).2 hD)
    have he1 : r.val + (k+1)*q = D+q := by rw [Nat.succ_mul, ← Nat.add_assoc, he]
    have hr : e (D+q) = e D := by
      apply le_antisymm (drop D)
      rw [← he1, ← he]
      exact (mono r hk).trans (hK r (k+1))
    have hx := hs D
    have hy := hs (D+q)
    simp only [e, Nat.add_mul] at hr hy
    apply Nat.eq_of_mul_eq_mul_left hq
    rw [Nat.mul_add]
    omega

lemma rational_slope_iff {a b d e : ℕ} (hd : 0 < d) (he : 0 < e) :
    (a : ℚ) / d ≤ (b : ℚ) / e ↔ e*a ≤ d*b := by
  rw [div_le_div_iff₀ (by exact_mod_cast hd) (by exact_mod_cast he)]
  rw [Nat.mul_comm e, Nat.mul_comm d]
  exact_mod_cast Iff.rfl

lemma finite_slope (H : ℕ → ℕ) (m : ℕ) (hm : 0 < m)
    (hc : ∀ D, 0 < D → ∃ d, 0 < d ∧ d ≤ m ∧ D * H d ≤ d * H D) :
    ∃ q, 0 < q ∧ q ≤ m ∧ ∀ D, D * H q ≤ q * H D := by
  classical
  let s := Finset.Icc 1 m
  have hn : s.Nonempty := ⟨1, Finset.mem_Icc.mpr ⟨by omega, hm⟩⟩
  obtain ⟨q, hq, hmin⟩ := Finset.exists_min_image s (fun d => (H d : ℚ) / d) hn
  have hb := Finset.mem_Icc.mp hq
  refine ⟨q, hb.1, hb.2, ?_⟩
  intro D
  obtain rfl | hd := Nat.eq_zero_or_pos D
  · simp
  obtain ⟨d, hdp, hdm, hD⟩ := hc D hd
  exact (rational_slope_iff hb.1 hd).1 ((hmin d (Finset.mem_Icc.mpr ⟨hdp, hdm⟩)).trans
    ((rational_slope_iff hdp hd).2 hD))

def adj {V : Type} [Preorder V] (u v : V) : Prop := u ≤ v ∨ v ≤ u

def wcost {V : Type} (r : V → ℕ) {l : ℕ} (p : Fin (l+1) → V) : ℕ :=
  ∑ i : Fin l, (r (p i.succ) - r (p i.castSucc))

def Terminal {V J : Type} [Preorder V] (P Z : V → J → Prop) (D : ℕ) (r : V → ℕ) : Prop :=
  ∀ (j : J) (l : ℕ) (p : Fin (l+1) → V), Function.Injective p →
    P (p 0) j → Z (p (Fin.last l)) j → (∀ i : Fin l, adj (p i.castSucc) (p i.succ)) →
    D ≤ wcost r p

lemma grid_potential {V J : Type} [Preorder V] {P Z : V → J → Prop} {D B : ℕ}
    (hf : Grid P Z D B) : ∃ r : V → ℕ, (∀ x, r x ≤ B) ∧ Monotone r ∧ Terminal P Z D r := by
  classical
  rcases isEmpty_or_nonempty J with hj | hj
  · exact ⟨fun _ => 0, fun _ => Nat.zero_le _, fun _ _ _ => le_rfl,
      fun j => (hj.false j).elim⟩
  obtain ⟨f, hfle, hfP, hfZ, hfanti, hfbudget⟩ := hf
  let S (x : V) : Set ℕ :=
    { c : ℕ | ∃ (l : ℕ) (p : Fin (l + 1) → V) (a : Fin l → J),
      (∀ i : Fin l, p i.castSucc ≤ p i.succ) ∧ p (Fin.last l) = x ∧
      c = Finset.univ.sum (fun i : Fin l => f (p i.castSucc) (a i) - f (p i.succ) (a i)) }
  have hSne : ∀ x, (S x).Nonempty := fun x =>
    ⟨0, 0, fun _ => x, fun i => i.elim0, fun i => i.elim0, rfl, by simp⟩
  have hSbdd : ∀ x, BddAbove (S x) := by
    intro x
    refine ⟨B, ?_⟩
    rintro c ⟨l, p, a, hsub, hlast, rfl⟩
    exact hfbudget l p a hsub
  let r (x : V) : ℕ := sSup (S x)
  have hr_mem : ∀ x, r x ∈ S x := fun x => Nat.sSup_mem (hSne x) (hSbdd x)
  have hr_le_B : ∀ x, r x ≤ B := fun x => csSup_le (hSne x) (by
    rintro c ⟨l, p, a, hsub, hlast, rfl⟩
    exact hfbudget l p a hsub)
  have hr_step : ∀ x y : V, x ≤ y → ∀ j : J, r x + (f x j - f y j) ≤ r y := by
    intro x y hxy j
    obtain ⟨l, p, a, hsub, hlast, hsum⟩ := hr_mem x
    let p' : Fin (l + 2) → V := Fin.snoc p y
    let a' : Fin (l + 1) → J := Fin.snoc a j
    have hsub' : ∀ i : Fin (l + 1), p' i.castSucc ≤ p' i.succ := by
      intro i
      refine Fin.lastCases ?_ ?_ i
      · simp only [p', Fin.succ_last, Fin.snoc_castSucc, Fin.snoc_last]
        rw [hlast]
        exact hxy
      · intro k
        simp only [p', Fin.succ_castSucc, Fin.snoc_castSucc]
        exact hsub k
    have hlast' : p' (Fin.last (l + 1)) = y := by simp [p']
    have hsum' : Finset.univ.sum (fun i : Fin (l + 1) => f (p' i.castSucc) (a' i) - f (p' i.succ) (a' i)) =
        r x + (f x j - f y j) := by
      rw [Fin.sum_univ_castSucc]
      have h1 : Finset.univ.sum (fun i : Fin l => f (p' i.castSucc.castSucc) (a' i.castSucc) - f (p' i.castSucc.succ) (a' i.castSucc)) =
          Finset.univ.sum (fun i : Fin l => f (p i.castSucc) (a i) - f (p i.succ) (a i)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [p', a', Fin.succ_castSucc, Fin.snoc_castSucc]
      rw [h1, ← hsum]
      simp only [p', a', Fin.succ_last, Fin.snoc_castSucc, Fin.snoc_last, hlast]
    exact le_csSup (hSbdd y) ⟨l + 1, p', a', hsub', hlast', hsum'.symm⟩
  have hr_mono : Monotone r := by
    intro x y hxy
    have := hr_step x y hxy hj.some
    omega
  refine ⟨r, hr_le_B, hr_mono, ?_⟩
  intro j l p _ hP hZ hadj
  have hedge : ∀ i : Fin l, (f (p i.castSucc) j : ℤ) - (f (p i.succ) j : ℤ) ≤
      ((r (p i.succ) - r (p i.castSucc) : ℕ) : ℤ) := by
    intro i
    rcases hadj i with hsub | hsub
    · have h1 := hr_step _ _ hsub j
      have h2 := hfanti _ _ hsub j
      have h3 := hr_mono hsub
      omega
    · have h2 := hfanti _ _ hsub j
      omega
  have hsum_int : (D : ℤ) ≤ ∑ i : Fin l, ((r (p i.succ) - r (p i.castSucc) : ℕ) : ℤ) := by
    have htel := sum_telescope_int (fun k : Fin (l + 1) => (f (p k) j : ℤ))
    rw [hfP (p 0) j hP, hfZ (p (Fin.last l)) j hZ] at htel
    calc (D : ℤ) = (D : ℤ) - (0 : ℕ) := by simp
      _ = ∑ i : Fin l, ((f (p i.castSucc) j : ℤ) - (f (p i.succ) j : ℤ)) := htel.symm
      _ ≤ ∑ i : Fin l, ((r (p i.succ) - r (p i.castSucc) : ℕ) : ℤ) := Finset.sum_le_sum fun i _ => hedge i
  exact_mod_cast hsum_int

lemma remove_loops {V : Type} [Preorder V] (r : V → ℕ) :
    ∀ (l : ℕ) (p : Fin (l + 1) → V),
      (∀ i : Fin l, adj (p i.castSucc) (p i.succ)) →
      ∃ (l' : ℕ) (p' : Fin (l' + 1) → V),
        Function.Injective p' ∧
        (∀ i : Fin l', adj (p' i.castSucc) (p' i.succ)) ∧
        p' 0 = p 0 ∧ p' (Fin.last l') = p (Fin.last l) ∧
        wcost r p' ≤ wcost r p := by
  intro l
  induction l using Nat.strong_induction_on with
  | ind l ih =>
    intro p hadj
    by_cases hinj : Function.Injective p
    · exact ⟨l, p, hinj, hadj, rfl, rfl, le_refl _⟩
    · simp only [Function.Injective, not_forall] at hinj
      obtain ⟨i1, i2, heq, hne⟩ := hinj
      have hpair : ∃ a b : Fin (l + 1), a.val < b.val ∧ p a = p b := by
        rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hgt
        · exact ⟨i1, i2, hlt, heq⟩
        · exact ⟨i2, i1, hgt, heq.symm⟩
      obtain ⟨a, b, hab, hpab⟩ := hpair
      let d := b.val - a.val
      have hd_pos : 0 < d := by omega
      have hd_le : d ≤ l := by omega
      let l1 := l - d
      have hl1_lt : l1 < l := by omega
      let idx : Fin (l1 + 1) → Fin (l + 1) := fun k =>
        if h : k.val ≤ a.val then ⟨k.val, by omega⟩
        else ⟨k.val + d, by omega⟩
      let q : Fin (l1 + 1) → V := fun k => p (idx k)
      have hq0 : q 0 = p 0 := by
        simp [q, idx]
      have hqlast : q (Fin.last l1) = p (Fin.last l) := by
        simp only [q, idx, Fin.val_last]
        split_ifs with h
        · have ha_eq : a.val = l1 := by omega
          have hb_eq : b = Fin.last l := Fin.ext (by dsimp only [Fin.val_last]; omega)
          have h1 : (⟨l1, by omega⟩ : Fin (l + 1)) = a := Fin.ext ha_eq.symm
          rw [h1, hpab, hb_eq]
        · congr 1
          exact Fin.ext (by dsimp only [Fin.val_last]; omega)
      have hq_edge : ∀ i : Fin l1,
          ∃ j : Fin l, (q i.castSucc = p j.castSucc ∧ q i.succ = p j.succ) ∧
            j.val = if i.val < a.val then i.val else i.val + d := by
        intro i
        by_cases hi : i.val < a.val
        · refine ⟨⟨i.val, by omega⟩, ⟨?_, ?_⟩, by simp [hi]⟩
          · simp only [q, idx, Fin.val_castSucc, show i.val ≤ a.val by omega, dite_true]; rfl
          · simp only [q, idx, Fin.val_succ, show i.val + 1 ≤ a.val by omega, dite_true]; rfl
        · refine ⟨⟨i.val + d, by omega⟩, ⟨?_, ?_⟩, by simp [hi]⟩
          · simp only [q, idx, Fin.val_castSucc]
            split_ifs with h
            · have hia : i.val = a.val := by omega
              have h1 : (⟨i.val, by omega⟩ : Fin (l + 1)) = a := Fin.ext hia
              rw [h1, hpab]
              congr 1; exact Fin.ext (by dsimp only [Fin.val_castSucc]; omega)
            · rfl
          · simp only [q, idx, Fin.val_succ, show ¬ (i.val + 1 ≤ a.val) by omega, dite_false]
            congr 1; exact Fin.ext (by dsimp only [Fin.val_succ]; omega)
      have hq_adj : ∀ i : Fin l1, adj (q i.castSucc) (q i.succ) := by
        intro i
        obtain ⟨j, ⟨h1, h2⟩, _⟩ := hq_edge i
        rw [h1, h2]
        exact hadj j
      have hq_cost : wcost r q ≤ wcost r p := by
        let emb : Fin l1 → Fin l := fun i =>
          if h : i.val < a.val then ⟨i.val, by omega⟩ else ⟨i.val + d, by omega⟩
        have hemb_inj : Function.Injective emb := by
          intro x y hxy
          have hv := congrArg Fin.val hxy
          simp only [emb] at hv
          split_ifs at hv <;> (dsimp only at hv; exact Fin.ext (by omega))
        have hterm : ∀ i : Fin l1, r (q i.succ) - r (q i.castSucc) = r (p (emb i).succ) - r (p (emb i).castSucc) := by
          intro i
          obtain ⟨j, ⟨h1, h2⟩, hj⟩ := hq_edge i
          have hjeq : j = emb i := Fin.ext (by simp [emb]; split_ifs at hj ⊢ <;> omega)
          rw [h1, h2, hjeq]
        calc wcost r q
            = ∑ i : Fin l1, (r (p (emb i).succ) - r (p (emb i).castSucc)) := Finset.sum_congr rfl fun i _ => hterm i
          _ = ∑ j ∈ Finset.univ.image emb, (r (p j.succ) - r (p j.castSucc)) :=
              (Finset.sum_image (f := fun j : Fin l => r (p j.succ) - r (p j.castSucc)) (fun x _ y _ h => hemb_inj h)).symm
          _ ≤ ∑ j : Fin l, (r (p j.succ) - r (p j.castSucc)) :=
              Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
      obtain ⟨l', p', hinj', hadj', hp'0, hp'last, hcost'⟩ := ih l1 hl1_lt q hq_adj
      exact ⟨l', p', hinj', hadj', hp'0.trans hq0, hp'last.trans hqlast, hcost'.trans hq_cost⟩

lemma potential_grid {V J : Type} [Preorder V] {P Z : V → J → Prop} {D B : ℕ}
    (r : V → ℕ) (hrB : ∀ x, r x ≤ B) (hrmono : Monotone r) (hrwalk : Terminal P Z D r) :
    Grid P Z D B := by
  classical
  let W (x : V) (j : J) : Set ℕ :=
    { c : ℕ | ∃ (l : ℕ) (p : Fin (l + 1) → V),
      (∀ i : Fin l, adj (p i.castSucc) (p i.succ)) ∧
      p 0 = x ∧ Z (p (Fin.last l)) j ∧ c = wcost r p }
  let f (x : V) (j : J) : ℕ :=
    if (W x j).Nonempty then min D (sInf (W x j)) else D
  have hfle : ∀ x j, f x j ≤ D := by
    intro x j
    simp only [f]
    split_ifs
    · exact min_le_left _ _
    · exact le_refl D
  have hfP : ∀ x j, P x j → f x j = D := by
    intro x j hP
    simp only [f]
    split_ifs with hne
    · have hmem : sInf (W x j) ∈ W x j := Nat.sInf_mem hne
      obtain ⟨l, p, hadj, hp0, hpZ, hcost⟩ := hmem
      obtain ⟨l', p', hinj', hadj', hp'0, hp'last, hcost'⟩ := remove_loops r l p hadj
      have hDle : D ≤ wcost r p' := hrwalk j l' p' hinj' (by rw [hp'0, hp0]; exact hP)
        (by rw [hp'last]; exact hpZ) hadj'
      have hDle2 : D ≤ sInf (W x j) := by omega
      exact min_eq_left hDle2
    · rfl
  have hfZ : ∀ x j, Z x j → f x j = 0 := by
    intro x j hZ
    have h0 : 0 ∈ W x j := ⟨0, fun _ => x, fun i => i.elim0, rfl, hZ, by simp [wcost]⟩
    have hne : (W x j).Nonempty := ⟨0, h0⟩
    have hinf0 : sInf (W x j) = 0 := Nat.eq_zero_of_le_zero (Nat.sInf_le h0)
    simp only [f, hne, ite_true, hinf0, Nat.min_zero]
  have htri : ∀ u v : V, adj u v → ∀ j : J, f u j ≤ f v j + (r v - r u) := by
    intro u v huv j
    by_cases hnev : (W v j).Nonempty
    · have hmem : sInf (W v j) ∈ W v j := Nat.sInf_mem hnev
      obtain ⟨l, p, hadj, hp0, hpZ, hcost⟩ := hmem
      let p' : Fin (l + 2) → V := Fin.cons u p
      have hadj' : ∀ i : Fin (l + 1), adj (p' i.castSucc) (p' i.succ) := by
        intro i
        refine Fin.cases ?_ ?_ i
        · simp only [p', Fin.castSucc_zero, Fin.succ_zero_eq_one, Fin.cons_zero, Fin.cons_one, hp0]
          exact huv
        · intro k
          simp only [p', Fin.castSucc_succ, Fin.cons_succ]
          exact hadj k
      have hcost' : wcost r p' = (r v - r u) + wcost r p := by
        simp only [wcost]
        rw [Fin.sum_univ_succ]
        simp only [p', Fin.castSucc_zero, Fin.succ_zero_eq_one, Fin.cons_zero, Fin.cons_one, hp0,
          Fin.castSucc_succ, Fin.cons_succ]
      have hmem_u : (r v - r u) + sInf (W v j) ∈ W u j :=
        ⟨l + 1, p', hadj', rfl, by simpa [p'] using hpZ, by rw [hcost', hcost]⟩
      have hneu : (W u j).Nonempty := ⟨_, hmem_u⟩
      have hle_inf : sInf (W u j) ≤ (r v - r u) + sInf (W v j) := Nat.sInf_le hmem_u
      simp only [f, hneu, hnev, ite_true]
      omega
    · simp only [f, hnev, ite_false]
      have := hfle u j
      simp only [f] at this
      omega
  have hfanti : ∀ x y : V, x ≤ y → ∀ j : J, f y j ≤ f x j := by
    intro x y hxy j
    have h := htri y x (Or.inr hxy) j
    simpa [Nat.sub_eq_zero_of_le (hrmono hxy)] using h
  have hdrop : ∀ x y : V, x ≤ y → ∀ j : J, f x j - f y j ≤ r y - r x := by
    intro x y hxy j
    have h := htri x y (Or.inl hxy) j
    omega
  refine ⟨f, hfle, hfP, hfZ, hfanti, ?_⟩
  intro l p a hsub
  calc Finset.univ.sum (fun i : Fin l => f (p i.castSucc) (a i) - f (p i.succ) (a i))
      ≤ Finset.univ.sum (fun i : Fin l => r (p i.succ) - r (p i.castSucc)) :=
        Finset.sum_le_sum fun i _ => hdrop (p i.castSucc) (p i.succ) (hsub i) (a i)
    _ = r (p (Fin.last l)) - r (p 0) :=
        sum_telescope_nat_mono (fun k => r (p k)) (fun i => hrmono (hsub i))
    _ ≤ r (p (Fin.last l)) := Nat.sub_le _ _
    _ ≤ B := hrB (p (Fin.last l))

noncomputable def common {n : ℕ} (g : Fin n → Fin n → Prop) (x : Finset (Fin n)) :
    Finset (Fin n) :=
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  Finset.univ.filter (fun j => ∀ i ∈ x, g i j)

lemma common_mem {n : ℕ} {g : Fin n → Fin n → Prop} {x : Finset (Fin n)} {j : Fin n} :
    j ∈ common g x ↔ ∀ i ∈ x, g i j := by simp [common]

lemma common_anti {n : ℕ} (g : Fin n → Fin n → Prop) : Antitone (common g) := by
  intro x y h j hj
  exact common_mem.2 (fun i hi => common_mem.1 hj i (h hi))

lemma double_ext {n : ℕ} {g : Fin n → Fin n → Prop} (hg : Symmetric g) (x : Finset (Fin n)) :
    x ⊆ common g (common g x) := by
  intro i hi
  exact common_mem.2 (fun j hj => hg (common_mem.1 hj i hi))

lemma triple_eq {n : ℕ} {g : Fin n → Fin n → Prop} (hg : Symmetric g) (x : Finset (Fin n)) :
    common g (common g (common g x)) = common g x :=
  le_antisymm (common_anti g (double_ext hg x)) (double_ext hg (common g x))

abbrev Closed {n : ℕ} (g : Fin n → Fin n → Prop) :=
  ↥((Finset.univ : Finset (Finset (Fin n))).image (common g))

noncomputable def closeV {n : ℕ} (g : Fin n → Fin n → Prop) (x : Finset (Fin n)) : Closed g :=
  ⟨common g (common g x), Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩

lemma close_mono {n : ℕ} (g : Fin n → Fin n → Prop) : Monotone (closeV g) := by
  intro x y h
  exact common_anti g (common_anti g h)

noncomputable def topV {n : ℕ} (g : Fin n → Fin n → Prop) : Closed g :=
  ⟨Finset.univ, Finset.mem_image.mpr ⟨∅, Finset.mem_univ _, by ext; simp [common]⟩⟩

lemma below_top {n : ℕ} (g : Fin n → Fin n → Prop) (x : Closed g) : x ≤ topV g :=
  Finset.subset_univ _

lemma close_grid {n : ℕ} {g : Fin n → Fin n → Prop} (hg : Symmetric g) (D B : ℕ) :
    Grid (fun x j => j ∈ common g x) (fun x j => j ∈ x) D B ↔
    Grid (fun x : Closed g => fun j => j ∈ common g x.val) (fun x j => j ∈ x.val) D B := by
  constructor
  · rintro ⟨f, hd, hp, hz, ha, hc⟩
    exact ⟨fun x j => f x.val j, fun x => hd x.val, fun x => hp x.val, fun x => hz x.val,
      fun x y h => ha x.val y.val h,
      fun l p a h => hc l (fun i => (p i).val) a h⟩
  · rintro ⟨f, hd, hp, hz, ha, hc⟩
    refine ⟨fun x j => f (closeV g x) j, fun x => hd _, ?_, ?_,
      fun x y h => ha _ _ (close_mono g h), fun l p a h => hc l (fun i => closeV g (p i)) a
        (fun i => close_mono g (h i))⟩
    · intro x j hj
      apply hp
      simpa only [closeV, triple_eq hg] using hj
    · intro x j hj
      exact hz _ _ (double_ext hg x hj)

lemma graph_grid {n : ℕ} {g : Fin n → Fin n → Prop} (hi : ∀ i, ¬g i i) (D : ℕ) :
    Grid (fun x j => j ∈ common g x) (fun x j => j ∈ x) D (D*n) := by
  classical
  let f (x : Finset (Fin n)) (j : Fin n) := if j ∈ x then 0 else D
  have hd x j : f x j ≤ D := by simp only [f]; split_ifs <;> omega
  refine ⟨f, hd, ?_, ?_, ?_, ?_⟩
  · intro x j hj
    have hjx : j ∉ x := fun h => hi j (common_mem.1 hj j h)
    simp [f, hjx]
  · intro x j hj
    simp [f, hj]
  · intro x y hxy j
    by_cases hj : j ∈ x
    · simp [f, hj, hxy hj]
    · simpa [f, hj] using hd y j
  · intro l p a hp
    have mono {x y : Finset (Fin n)} (hxy : x ⊆ y) : D*x.card ≤ D*y.card :=
      Nat.mul_le_mul_left D (Finset.card_le_card hxy)
    calc ∑ i : Fin l, (f (p i.castSucc) (a i) - f (p i.succ) (a i)) ≤
        ∑ i : Fin l, (D*(p i.succ).card - D*(p i.castSucc).card) := by
          apply Finset.sum_le_sum
          intro i _
          by_cases h : p i.castSucc = p i.succ
          · simp [h]
          · have hs : (p i.castSucc).card + 1 ≤ (p i.succ).card :=
              Finset.card_lt_card (lt_of_le_of_ne (hp i) h)
            have hx := Nat.mul_le_mul_left D hs
            rw [Nat.mul_succ] at hx
            have := hd (p i.castSucc) (a i)
            omega
      _ = D*(p (Fin.last l)).card - D*(p 0).card :=
        sum_telescope_nat_mono (fun k => D*(p k).card) (fun i => mono (hp i))
      _ ≤ D*n := by
        have hx := Nat.mul_le_mul_left D (Finset.card_le_univ (p (Fin.last l)))
        simp only [Fintype.card_fin] at hx
        omega

lemma row_pivot {V C : Type} [Fintype V] [Fintype C] (a : C → V → ℚ) (b : C → ℚ)
    (z v : V → ℚ) (hz : ∀ c, b c ≤ a c ⬝ᵥ z) (hblock : ∃ c, a c ⬝ᵥ v < 0) :
    ∃ (t : ℚ) (c : C), 0 ≤ t ∧ a c ⬝ᵥ v ≠ 0 ∧ a c ⬝ᵥ (z + t • v) = b c ∧
      ∀ i, b i ≤ a i ⬝ᵥ (z + t • v) := by
  classical
  let T (c : C) := (b c - a c ⬝ᵥ z) / (a c ⬝ᵥ v)
  obtain ⟨i0, hi0⟩ := hblock
  obtain ⟨c, hc, hmin⟩ := Finset.exists_min_image (Finset.univ.filter (fun c => a c ⬝ᵥ v < 0))
    T ⟨i0, by simp [hi0]⟩
  have hn : a c ⬝ᵥ v < 0 := (Finset.mem_filter.mp hc).2
  have ht : 0 ≤ T c := (div_nonneg_iff.mpr (Or.inr ⟨sub_nonpos.mpr (hz c), hn.le⟩))
  have eqn (i : C) (hi : a i ⬝ᵥ v ≠ 0) : T i * (a i ⬝ᵥ v) = b i - a i ⬝ᵥ z :=
    div_mul_cancel₀ _ hi
  refine ⟨T c, c, ht, hn.ne, ?_, ?_⟩
  · rw [dotProduct_add, dotProduct_smul, smul_eq_mul, eqn c hn.ne]
    ring
  · intro i
    rw [dotProduct_add, dotProduct_smul, smul_eq_mul]
    by_cases hi : a i ⬝ᵥ v < 0
    · have h := mul_le_mul_of_nonpos_right (hmin i (by simp [hi])) hi.le
      rw [eqn i hi.ne] at h
      linarith
    · linarith [hz i, mul_nonneg ht (le_of_not_gt hi)]

lemma row_slide {V C : Type} [Fintype V] [Fintype C] (a : C → V → ℚ) (b : C → ℚ)
    (p : V) (z v : V → ℚ) (hz : ∀ c, b c ≤ a c ⬝ᵥ z) (hv : v ≠ 0)
    (hblock : ∀ w : V → ℚ, w ≠ 0 → ∃ c, a c ⬝ᵥ w < 0) :
    ∃ (t : ℚ) (c : C), (z + t • v) p ≤ z p ∧ a c ⬝ᵥ v ≠ 0 ∧
      a c ⬝ᵥ (z + t • v) = b c ∧ ∀ i, b i ≤ a i ⬝ᵥ (z + t • v) := by
  by_cases h : v p ≤ 0
  · obtain ⟨t,c,ht,hv',hc,ha⟩ := row_pivot a b z v hz (hblock v hv)
    refine ⟨t,c,?_,hv',hc,ha⟩
    change z p + t * v p ≤ z p
    linarith [mul_nonpos_of_nonneg_of_nonpos ht h]
  · obtain ⟨t,c,ht,hv',hc,ha⟩ := row_pivot a b z (-v) hz (hblock (-v) (neg_ne_zero.mpr hv))
    refine ⟨-t,c,?_,?_,?_,?_⟩
    · change z p + -t * v p ≤ z p
      linarith [mul_nonneg ht (le_of_not_ge h)]
    · simpa only [dotProduct_neg, neg_ne_zero] using hv'
    · simpa only [neg_smul, smul_neg] using hc
    · simpa only [neg_smul, smul_neg] using ha

lemma row_basis {V C : Type} [Fintype V] [Fintype C] (a : C → V → ℚ) (b : C → ℚ)
    (hblock : ∀ v : V → ℚ, v ≠ 0 → ∃ c, a c ⬝ᵥ v < 0)
    (p0 : V) (z0 : V → ℚ) (hz0 : ∀ c, b c ≤ a c ⬝ᵥ z0) (k : ℕ) (hk : k ≤ Fintype.card V) :
    ∃ (z : V → ℚ) (ι : Fin k → C), (∀ c, b c ≤ a c ⬝ᵥ z) ∧ z p0 ≤ z0 p0 ∧
      LinearIndependent ℚ (fun i => a (ι i)) ∧ ∀ i, a (ι i) ⬝ᵥ z = b (ι i) := by
  classical
  induction k with
  | zero => exact ⟨z0, Fin.elim0, hz0, le_rfl, linearIndependent_empty_type, fun i => i.elim0⟩
  | succ k ih =>
    obtain ⟨z, ι, hz, hprop, hli, htight⟩ := ih (by omega)
    set p := Submodule.span ℚ (Set.range fun i => a (ι i)) with hp
    have hlt : p < ⊤ := by
      rw [lt_top_iff_ne_top]
      intro htop
      have h1 := finrank_span_eq_card hli
      rw [← hp, htop, finrank_top, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h1
      omega
    obtain ⟨f, hf0, hf⟩ := Submodule.exists_le_ker_of_lt_top p hlt
    set v : V → ℚ := fun j => f (fun j' => if j = j' then 1 else 0) with hv
    have hfv : ∀ x, f x = x ⬝ᵥ v := by
      intro x
      rw [LinearMap.pi_apply_eq_sum_univ f x]
      simp [dotProduct, hv]
    have hv0 : v ≠ 0 := by
      intro h
      exact hf0 (LinearMap.ext fun x => by rw [hfv, h]; simp)
    have hker : ∀ i, a (ι i) ⬝ᵥ v = 0 := by
      intro i
      rw [← hfv]
      exact LinearMap.mem_ker.mp (hf (Submodule.subset_span ⟨i, rfl⟩))
    obtain ⟨t,c,ht,hcv,htc,hfeas⟩ := row_slide a b p0 z v hz hv0 hblock
    refine ⟨z + t • v, Fin.cons c ι, hfeas, ht.trans hprop, ?_, ?_⟩
    · have hcons : (fun i => a ((Fin.cons c ι : Fin (k + 1) → C) i)) =
          Fin.cons (a c) (fun i => a (ι i)) := by
        funext i
        refine Fin.cases ?_ (fun i => ?_) i <;> simp
      rw [hcons, linearIndependent_finCons]
      refine ⟨hli, fun hmem => hcv ?_⟩
      rw [← hfv]
      exact LinearMap.mem_ker.mp (hf hmem)
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · simpa using htc
      · simp only [Fin.cons_succ]
        rw [dotProduct_add, dotProduct_smul, hker, htight]
        simp

theorem detBound {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℤ)
    (h : ∀ i j, (A i j).natAbs ≤ 1) : A.det.natAbs ≤ (Fintype.card ι).factorial := by
  classical
  have term (σ : Equiv.Perm ι) : |Equiv.Perm.sign σ • ∏ i, A (σ i) i| ≤ (1 : ℤ) := by
    have prod (t : Finset ι) : (∏ i ∈ t, A (σ i) i).natAbs ≤ 1 := by
      induction t using Finset.induction_on with
      | empty => simp
      | insert i t hi ih =>
        rw [Finset.prod_insert hi, Int.natAbs_mul]
        exact Nat.mul_le_mul (h _ _) ih
    have z : |∏ i, A (σ i) i| ≤ (1 : ℤ) := by
      rw [← Int.natCast_natAbs]
      exact_mod_cast prod Finset.univ
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> simpa [hs, Units.smul_def] using z
  have d : |A.det| ≤ ((Fintype.card ι).factorial : ℤ) := calc
    |A.det| = |∑ σ : Equiv.Perm ι, Equiv.Perm.sign σ • ∏ i, A (σ i) i| := by rw [Matrix.det_apply]
    _ ≤ ∑ σ : Equiv.Perm ι, |Equiv.Perm.sign σ • ∏ i, A (σ i) i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : Equiv.Perm ι, (1 : ℤ) := Finset.sum_le_sum fun σ _ => term σ
    _ = _ := by simp [Fintype.card_perm]
  rw [← Int.natCast_natAbs] at d
  exact_mod_cast d

theorem cramerMultiple {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℤ)
    (h : ∀ i j, (A i j).natAbs ≤ 1) (hd : A.det ≠ 0) (b : ι → ℤ) :
    ∃ q : ℕ, 0 < q ∧ q ≤ (Fintype.card ι).factorial ∧
      ∃ z : ι → ℤ, A.mulVec z = (q : ℤ) • b := by
  refine ⟨A.det.natAbs, Int.natAbs_pos.mpr hd, detBound A h, ?_⟩
  rw [Int.natCast_natAbs]
  by_cases hn : 0 ≤ A.det
  · exact ⟨A.cramer b, by rw [Matrix.mulVec_cramer,abs_of_nonneg hn]⟩
  · exact ⟨-(A.cramer b), by rw [Matrix.mulVec_neg,Matrix.mulVec_cramer,abs_of_neg (lt_of_not_ge hn),neg_smul]⟩

lemma preserve_rows {V : Type} [Fintype V] (z0 : V → ℚ) (p : V) :
    ∃ q : ℕ, 0 < q ∧ q ≤ (Fintype.card V).factorial ∧ ∃ N : V → ℤ,
      (N p : ℚ) ≤ (q : ℚ) * z0 p ∧
      ∀ (w : V → ℤ) (b : ℤ), (∀ j, |w j| ≤ 1) →
        (b : ℚ) ≤ (fun j => (w j : ℚ)) ⬝ᵥ z0 → (q : ℤ) * b ≤ w ⬝ᵥ N := by
  classical
  let C := V → ↥(Finset.Icc (-1 : ℤ) 1)
  let R (c : C) (j : V) : ℤ := (c j).val
  let a (c : C) (j : V) : ℚ := R c j
  let b (c : C) : ℤ := ⌊a c ⬝ᵥ z0⌋
  have rows (w : V → ℤ) (hw : ∀ j, |w j| ≤ 1) : ∃ c : C, R c = w :=
    ⟨fun j => ⟨w j, Finset.mem_Icc.mpr (abs_le.mp (hw j))⟩, rfl⟩
  have hblock (v : V → ℚ) (hv : v ≠ 0) : ∃ c : C, a c ⬝ᵥ v < 0 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
    change v i ≠ 0 at hi
    have single (d : ℤ) (hd : |d| ≤ 1) : ∃ c : C, a c ⬝ᵥ v = (d : ℚ) * v i := by
      obtain ⟨c, hc⟩ := rows (fun j => if i = j then d else 0) (by intro j; split_ifs <;> simp [hd])
      refine ⟨c, ?_⟩
      simp [a, hc, dotProduct, apply_ite, ite_mul]
    rcases lt_or_gt_of_ne hi with hn | hp
    · obtain ⟨c, hc⟩ := single 1 (by norm_num)
      exact ⟨c, by simpa [hc] using hn⟩
    · obtain ⟨c, hc⟩ := single (-1) (by norm_num)
      exact ⟨c, by simp [hc]; linarith⟩
  obtain ⟨z, ι, hz, htop, hli, ht⟩ := row_basis a (fun c => (b c : ℚ)) hblock p z0
    (fun c => Int.floor_le _) (Fintype.card V) le_rfl
  let e := Fintype.equivFin V
  let I : V → C := fun j => ι (e j)
  let A : Matrix V V ℤ := Matrix.of fun i => R (I i)
  let B : V → ℤ := fun i => b (I i)
  let M : Matrix V V ℚ := Matrix.of fun i => a (I i)
  have hm : M = A.map (Int.castRingHom ℚ) := rfl
  have hu : IsUnit M := by
    rw [← Matrix.linearIndependent_row_iff_isUnit]
    exact hli.comp _ e.injective
  have hd : A.det ≠ 0 := by
    have h := ((Matrix.isUnit_iff_isUnit_det M).mp hu).ne_zero
    have hdet : M.det = (A.det : ℚ) := by
      rw [hm]
      exact ((Int.castRingHom ℚ).map_det A).symm
    rw [hdet] at h
    exact fun h0 => h (by simp [h0])
  have hcoeff (i j : V) : (A i j).natAbs ≤ 1 := by
    have hj := Finset.mem_Icc.mp ((I i j).property)
    have hx : |A i j| ≤ (1 : ℤ) := abs_le.mpr hj
    rw [← Int.natCast_natAbs] at hx
    exact_mod_cast hx
  obtain ⟨q, hq, hqm, N, hN⟩ := cramerMultiple A hcoeff hd B
  have hMz : M *ᵥ z = fun i => (B i : ℚ) := funext fun i => ht (e i)
  have hcast : M *ᵥ (fun j => (N j : ℚ)) = M *ᵥ ((q : ℚ) • z) := by
    rw [Matrix.mulVec_smul, hMz]
    funext i
    have h : ((A *ᵥ N) i : ℚ) = (((q : ℤ) • B) i : ℚ) := by rw [hN]
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h ⊢
    push_cast at h
    simpa [M, A, a] using h
  have hNz := Matrix.mulVec_injective_of_isUnit hu hcast
  have scal (i : V) : (N i : ℚ) = (q : ℚ) * z i := congrFun hNz i
  refine ⟨q, hq, hqm, N, ?_, ?_⟩
  · rw [scal p]
    exact mul_le_mul_of_nonneg_left htop (Nat.cast_nonneg q)
  · intro w d hw hw0
    obtain ⟨c, hc⟩ := rows w hw
    have hβ : d ≤ b c := Int.le_floor.mpr (by simpa only [a, hc] using hw0)
    have hdz : (d : ℚ) ≤ a c ⬝ᵥ z := (by exact_mod_cast hβ : (d : ℚ) ≤ (b c : ℚ)).trans (hz c)
    have hdot : ((w ⬝ᵥ N : ℤ) : ℚ) = (q : ℚ) * (a c ⬝ᵥ z) := by
      simp only [dotProduct, Int.cast_sum, Int.cast_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      simp only [scal, a, hc]
      ring
    have hh : (q : ℚ) * (d : ℚ) ≤ ((w ⬝ᵥ N : ℤ) : ℚ) := by
      rw [hdot]
      exact mul_le_mul_of_nonneg_left hdz (Nat.cast_nonneg q)
    exact_mod_cast hh

noncomputable def signed {V : Type} [DecidableEq V] (u v : Finset V) (x : V) : ℤ :=
  (if x ∈ u then 1 else 0) - (if x ∈ v then 1 else 0)

lemma signed_bound {V : Type} [DecidableEq V] (u v : Finset V) (x : V) : |signed u v x| ≤ 1 := by
  simp only [signed]
  split_ifs <;> norm_num

lemma signed_dot {V : Type} [Fintype V] [DecidableEq V] (u v : Finset V) (r : V → ℤ) :
    signed u v ⬝ᵥ r = (∑ x ∈ u, r x) - ∑ x ∈ v, r x := by
  simp [signed, dotProduct, sub_mul, Finset.sum_sub_distrib, ite_mul]

lemma walk_row {V : Type} [Fintype V] [Preorder V] {l : ℕ} (p : Fin (l+1) → V)
    (hi : Function.Injective p) (ha : ∀ i : Fin l, adj (p i.castSucc) (p i.succ)) :
    ∃ w : V → ℤ, (∀ x, |w x| ≤ 1) ∧ ∀ r : V → ℕ, Monotone r →
      w ⬝ᵥ (fun x => (r x : ℤ)) = (wcost r p : ℤ) := by
  classical
  let s := Finset.univ.filter (fun i : Fin l => p i.castSucc ≤ p i.succ)
  let u := s.image (fun i => p i.succ)
  let v := s.image (fun i => p i.castSucc)
  refine ⟨signed u v, signed_bound u v, ?_⟩
  intro r hr
  have hup : Function.Injective (fun i : Fin l => p i.succ) := hi.comp (Fin.succ_injective l)
  have hdown : Function.Injective (fun i : Fin l => p i.castSucc) := hi.comp (Fin.castSucc_injective l)
  rw [signed_dot]
  dsimp only [u,v]
  rw [Finset.sum_image (fun _ _ _ _ h => hup h), Finset.sum_image (fun _ _ _ _ h => hdown h),
    ← Finset.sum_sub_distrib]
  simp only [s, Finset.sum_filter, wcost, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : p i.castSucc ≤ p i.succ
  · simp [h, Nat.cast_sub (hr h)]
  · have hd : p i.succ ≤ p i.castSucc := (ha i).resolve_left h
    simp [h, Nat.sub_eq_zero_of_le (hr hd)]

lemma rescale_rows {V : Type} [Fintype V] (r : V → ℕ) (p : V) {D : ℕ} (hD : 0 < D) :
    ∃ q : ℕ, 0 < q ∧ q ≤ (Fintype.card V).factorial ∧ ∃ N : V → ℤ,
      (D : ℤ) * N p ≤ (q : ℤ) * r p ∧
      ∀ (w : V → ℤ) (b : ℤ), (∀ j, |w j| ≤ 1) →
        (D : ℤ) * b ≤ w ⬝ᵥ (fun i => (r i : ℤ)) → (q : ℤ) * b ≤ w ⬝ᵥ N := by
  let z0 : V → ℚ := fun i => (r i : ℚ) / D
  obtain ⟨q,hq,hm,N,hp,hrow⟩ := preserve_rows z0 p
  have hd : (0 : ℚ) < D := by exact_mod_cast hD
  refine ⟨q,hq,hm,N,?_,?_⟩
  · change (N p : ℚ) ≤ (q : ℚ) * ((r p : ℚ) / D) at hp
    rw [← mul_div_assoc, le_div_iff₀ hd] at hp
    rw [mul_comm (D : ℤ)]
    exact_mod_cast hp
  · intro w b hw hb
    apply hrow w b hw
    have heq : (fun i => (w i : ℚ)) ⬝ᵥ z0 = ((w ⬝ᵥ (fun i => (r i : ℤ)) : ℤ) : ℚ) / D := by
      simp [z0, dotProduct, Finset.sum_div, mul_div_assoc]
    rw [heq, le_div_iff₀ hd]
    rw [mul_comm (D : ℤ)] at hb
    exact_mod_cast hb

lemma improve_grid {V J : Type} [Preorder V] [Fintype V] (p : V) (ht : ∀ x, x ≤ p)
    {P Z : V → J → Prop} {D B : ℕ} (hd : 0 < D) (hg : Grid P Z D B) :
    ∃ (q b : ℕ), 0 < q ∧ q ≤ (Fintype.card V).factorial ∧ Grid P Z q b ∧ D*b ≤ q*B := by
  classical
  obtain ⟨r,hB,hr,hterm⟩ := grid_potential hg
  obtain ⟨q,hq,hm,N,hp,hrows⟩ := rescale_rows r p hd
  have hn (x : V) : 0 ≤ N x := by
    have h := hrows (signed {x} ∅) 0 (signed_bound _ _) (by simp [signed_dot])
    simpa [signed_dot] using h
  let s (x : V) := (N x).toNat
  have hcast (x : V) : (s x : ℤ) = N x := Int.toNat_of_nonneg (hn x)
  have hs : Monotone s := by
    intro x y h
    have h0 := hrows (signed {y} {x}) 0 (signed_bound _ _) (by simp [signed_dot, hr h])
    have h1 : N x ≤ N y := by simpa [signed_dot] using h0
    exact Int.toNat_le_toNat h1
  refine ⟨q,s p,hq,hm,potential_grid s (fun x => hs (ht x)) hs ?_,?_⟩
  · intro j l path hi hpos hzero ha
    obtain ⟨w, hw, he⟩ := walk_row path hi ha
    have h0 : (D : ℤ) * 1 ≤ w ⬝ᵥ (fun i => (r i : ℤ)) := by
      rw [mul_one, he r hr]
      exact_mod_cast hterm j l path hi hpos hzero ha
    have h1 := hrows w 1 hw h0
    rw [mul_one, ← (funext hcast : (fun i => (s i : ℤ)) = N), he s hs] at h1
    exact_mod_cast h1
  · have h : (D : ℤ) * (s p : ℤ) ≤ (q : ℤ) * B := by
      rw [hcast p]
      exact hp.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hB p) (Nat.cast_nonneg q))
    exact_mod_cast h

end PEqualNP.Outside.L_meta_49528

open PEqualNP.Outside.L_meta_49528

theorem PEqualNP.Outside.L_meta_49528 : (letI : ∀ p : Prop, Decidable p := Classical.propDecidable
∀ (n : Nat) (g : Fin n → Fin n → Prop),
  Symmetric g → (∀ i, ¬g i i) →
  let X := Finset (Fin n)
  let C := fun (x : X) => (Finset.univ : X).filter (fun j => ∀ i ∈ x, g i j)
  let M := ((Finset.univ : Finset X).image C).card
  let admits := fun (D B : Nat) =>
    ∃ f : X → Fin n → Nat,
      (∀ x j, f x j ≤ D) ∧ (∀ x j, j ∈ C x → f x j = D) ∧
      (∀ x j, j ∈ x → f x j = 0) ∧ (∀ x y, x ⊆ y → ∀ j, f y j ≤ f x j) ∧
      ∀ (l : Nat) (p : Fin (l+1) → X) (a : Fin l → Fin n),
        (∀ i : Fin l, p i.castSucc ⊆ p i.succ) →
        Finset.univ.sum (fun i : Fin l => f (p i.castSucc) (a i) - f (p i.succ) (a i)) ≤ B
  ∃ H : Nat → Nat, (∀ D B, admits D B ↔ H D ≤ B) ∧ H 0 = 0 ∧
    (∀ u v, H (u+v) ≤ H u + H v) ∧
    ∃ q : Nat, 0 < q ∧ q ≤ Nat.factorial M ∧
      (∀ D, D * H q ≤ q * H D) ∧ (∀ k, H (k*q) = k*H q) ∧
      ∃ T : Nat, ∀ D, T ≤ D → H (D+q) = H D + H q) := by
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  intro n g hg hi X C M admits
  let A (D B : ℕ) := Grid (fun x j => j ∈ common g x) (fun x j => j ∈ x) D B
  have he (D B : ℕ) : admits D B ↔ A D B := Iff.rfl
  obtain ⟨H,hc,hz,ha⟩ := height_exists A (fun D => ⟨D*n,graph_grid hi D⟩)
    (fun _ _ _ h h' => grid_mono h h') (grid_zero _ _) (fun _ _ _ _ h k => grid_add h k)
  have hcard : Fintype.card (Closed g) = M := by
    unfold Closed
    rw [Fintype.card_coe]
    dsimp only [M, C, X, common]
    congr 1 <;> congr 1 <;> apply Subsingleton.elim
  have hsmall (D : ℕ) (hd : 0 < D) : ∃ q, 0 < q ∧ q ≤ M.factorial ∧ D * H q ≤ q * H D := by
    obtain ⟨q,b,hq,hm,hgrid,hbudget⟩ := improve_grid (topV g) (below_top g) hd
      ((close_grid hg D (H D)).1 ((hc D (H D)).2 le_rfl))
    have hb := (hc q b).1 ((close_grid hg q b).2 hgrid)
    exact ⟨q,hq,hcard ▸ hm,(Nat.mul_le_mul_left D hb).trans hbudget⟩
  obtain ⟨q,hq,hm,hs⟩ := finite_slope H M.factorial (Nat.factorial_pos _) hsmall
  exact ⟨H,fun D B => (he D B).trans (hc D B),hz,ha,q,hq,hm,hs,semigroup_tail H hz ha q hq hs⟩
