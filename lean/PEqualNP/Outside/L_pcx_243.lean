import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_243_aux

def Val (d : ℕ) (T : Finset ℕ) (l : ℕ → ℕ) : Prop :=
  Set.InjOn l (T : Set ℕ) ∧ (∀ p ∈ T, l p < d) ∧
  ∀ p ∈ T, p ≤ 2 ^ l p ∨ ∃ q ∈ T, q < p ∧ l p < l q ∧ p ≤ q + 2 ^ l p

def Good (d : ℕ) (T : Finset ℕ) : Prop := ∃ l, Val d T l

theorem two_pow_lt {a b : ℕ} (h : a < b) : 2 * 2 ^ a ≤ 2 ^ b := by
  have h1 := Nat.pow_le_pow_right (by norm_num : 0 < 2) (Nat.succ_le_of_lt h)
  rw [pow_succ] at h1
  omega

theorem good_empty (d : ℕ) : Good d ∅ := by
  refine ⟨fun _ => 0, ?_, ?_, ?_⟩
  · intro a ha
    simp at ha
  · intro p hp
    simp at hp
  · intro p hp
    simp at hp

theorem val_bound {d : ℕ} {T : Finset ℕ} {l : ℕ → ℕ} (h : Val d T l) :
    ∀ p, p ∈ T → p + 2 ^ l p ≤ 2 ^ d := by
  intro p
  induction p using Nat.strong_induction_on with
  | _ p ih =>
    intro hp
    have hd := two_pow_lt (h.2.1 p hp)
    rcases h.2.2 p hp with hb | ⟨q, hq, hqp, hlq, hpq⟩
    · omega
    · have h1 := ih q hqp hq
      have h2 := two_pow_lt hlq
      omega

theorem good_bound {d : ℕ} {T : Finset ℕ} (h : Good d T) {p : ℕ} (hp : p ∈ T) : p + 1 ≤ 2 ^ d := by
  obtain ⟨l, h⟩ := h
  have h1 := val_bound h p hp
  have h2 := Nat.one_le_two_pow (n := l p)
  omega

theorem val_uniq {d : ℕ} {T : Finset ℕ} {l : ℕ → ℕ} (h : Val d T l) :
    ∀ p, p ∈ T → p + 2 ^ l p = 2 ^ d →
      ∀ j, l p ≤ j → j < d → ∃ s ∈ T, l s = j ∧ s + 2 ^ j = 2 ^ d := by
  intro p
  induction p using Nat.strong_induction_on with
  | _ p ih =>
    intro hp he j hj hjd
    rcases Nat.eq_or_lt_of_le hj with rfl | hlt
    · exact ⟨p, hp, rfl, he⟩
    · rcases h.2.2 p hp with hb | ⟨q, hq, hqp, hlq, hpq⟩
      · have h1 := two_pow_lt hlt
        have h2 := two_pow_lt hjd
        have h3 := Nat.one_le_two_pow (n := j)
        omega
      · have hbq := val_bound h q hq
        have h1 := two_pow_lt hlq
        have e1 : 2 ^ (l p + 1) = 2 ^ l q := by
          rw [pow_succ]
          omega
        have e2 : l p + 1 = l q := Nat.pow_right_injective (le_refl 2) e1
        exact ih q hqp hq (by omega) j (by omega) hjd

theorem top_arith {j d : ℕ} (hjd : j < d) (he : 2 + 2 ^ j = 2 ^ d) : d = 2 := by
  have h3 := two_pow_lt hjd
  have hj1 : j ≤ 1 := by
    by_contra hc
    have h4 := two_pow_lt (show 1 < j by omega)
    norm_num at h4
    omega
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
  interval_cases j
  · rw [pow_succ] at he
    omega
  · have e : 2 ^ (k + 1) = 2 ^ 2 := by
      norm_num at he ⊢
      omega
    exact Nat.pow_right_injective (le_refl 2) e

theorem good_top {d : ℕ} {T : Finset ℕ} (h : Good d T) {p : ℕ} (hp : p ∈ T) (hpd : p + 1 = 2 ^ d)
    (h2 : 2 ∈ T) : d = 2 := by
  obtain ⟨l, h⟩ := h
  have hb := val_bound h p hp
  have h1 := Nat.one_le_two_pow (n := l p)
  have he : p + 2 ^ l p = 2 ^ d := by omega
  obtain ⟨s, hs, hls, hse⟩ := val_uniq h p hp he (l 2) (by
    by_contra hc
    have h4 := two_pow_lt (show 0 < l p by omega)
    norm_num at h4
    omega) (h.2.1 2 h2)
  have e : s = 2 := h.1 hs h2 hls
  subst e
  exact top_arith (h.2.1 2 h2) hse

theorem val_chain {d : ℕ} {T : Finset ℕ} {l : ℕ → ℕ} (h : Val d T l) (lam : ℕ)
    (hlam : ∀ u ∈ T, l u ≠ lam) :
    ∀ x, x ∈ T → l x < lam →
      (x + 2 ^ l x ≤ 2 ^ lam) ∨ ∃ q ∈ T, q < x ∧ lam < l q ∧ x + 2 ^ l x ≤ q + 2 ^ lam := by
  intro x
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    intro hx hlx
    have h0 := two_pow_lt hlx
    rcases h.2.2 x hx with hb | ⟨q1, hq1, hq1x, hl1, hxq⟩
    · left
      omega
    · have h1 := two_pow_lt hl1
      rcases lt_trichotomy (l q1) lam with hlt | heq | hgt
      · rcases ih q1 hq1x hq1 hlt with hb | ⟨q, hq, hqq, hlq, hle⟩
        · left
          omega
        · right
          exact ⟨q, hq, by omega, hlq, by omega⟩
      · exact absurd heq (hlam q1 hq1)
      · right
        have h2 := two_pow_lt hgt
        exact ⟨q1, hq1, hq1x, hgt, by omega⟩

theorem exists_free {d : ℕ} {T : Finset ℕ} (l : ℕ → ℕ) (hc : T.card < d) :
    ∃ lam, lam < d ∧ ∀ u ∈ T, l u ≠ lam := by
  by_contra hcon
  have hsub : Finset.range d ⊆ T.image l := by
    intro a ha
    by_contra hne
    exact hcon ⟨a, Finset.mem_range.mp ha, fun u hu e => hne (Finset.mem_image.mpr ⟨u, hu, e⟩)⟩
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_image_le (s := T) (f := l)
  rw [Finset.card_range] at h1
  omega

theorem insert_wit {d : ℕ} {T : Finset ℕ} {l : ℕ → ℕ} (h : Val d T l) {p lam : ℕ}
    (hlam : ∀ u ∈ T, l u ≠ lam) (hen : p = 1 ∨ ∃ x ∈ T, p = x + 1) :
    p ≤ 2 ^ lam ∨ ∃ q ∈ T, q < p ∧ lam < l q ∧ p ≤ q + 2 ^ lam := by
  have h1 := Nat.one_le_two_pow (n := lam)
  rcases hen with rfl | ⟨x, hx, rfl⟩
  · left
    exact h1
  · rcases lt_or_gt_of_ne (hlam x hx) with hlt | hgt
    · have h2 := Nat.one_le_two_pow (n := l x)
      rcases val_chain h lam hlam x hx hlt with hb | ⟨q, hq, hqx, hlq, hle⟩
      · left
        omega
      · right
        exact ⟨q, hq, by omega, hlq, by omega⟩
    · right
      exact ⟨x, hx, by omega, hgt, by omega⟩

theorem good_insert {d : ℕ} {T : Finset ℕ} (h : Good d T) {p : ℕ} (hp : p ∉ T)
    (hen : p = 1 ∨ ∃ x ∈ T, p = x + 1) (hc : T.card < d) : Good d (insert p T) := by
  obtain ⟨l, h⟩ := h
  obtain ⟨lam, hlamd, hlam⟩ := exists_free l hc
  have hup : ∀ u ∈ T, Function.update l p lam u = l u := fun u hu =>
    Function.update_of_ne (show u ≠ p from fun e => hp (e ▸ hu)) _ _
  have hupp : Function.update l p lam p = lam := Function.update_self _ _ _
  refine ⟨Function.update l p lam, ?_, ?_, ?_⟩
  · intro a ha b hb hab
    have ha' : a ∈ insert p T := ha
    have hb' : b ∈ insert p T := hb
    rcases Finset.mem_insert.mp ha' with ea | haT <;> rcases Finset.mem_insert.mp hb' with eb | hbT
    · rw [ea, eb]
    · rw [ea, hupp, hup b hbT] at hab
      exact absurd hab.symm (hlam b hbT)
    · rw [eb, hupp, hup a haT] at hab
      exact absurd hab (hlam a haT)
    · rw [hup a haT, hup b hbT] at hab
      exact h.1 haT hbT hab
  · intro u hu
    rcases Finset.mem_insert.mp hu with eu | huT
    · rw [eu, hupp]
      exact hlamd
    · rw [hup u huT]
      exact h.2.1 u huT
  · intro u hu
    rcases Finset.mem_insert.mp hu with eu | huT
    · rw [eu, hupp]
      rcases insert_wit h hlam hen with hb | ⟨q, hq, hqp, hlq, hle⟩
      · left
        exact hb
      · right
        exact ⟨q, Finset.mem_insert_of_mem hq, hqp, by rw [hup q hq]; exact hlq, hle⟩
    · rw [hup u huT]
      rcases h.2.2 u huT with hb | ⟨q, hq, hqu, hlq, hle⟩
      · left
        exact hb
      · right
        exact ⟨q, Finset.mem_insert_of_mem hq, hqu, by rw [hup q hq]; exact hlq, hle⟩

theorem val_E {d : ℕ} {U : Finset ℕ} {l : ℕ → ℕ} (h : Val d U l) (lam c : ℕ) (hc : c < lam) :
    ∀ x, x ∈ U → (∀ u ∈ U, u ≤ x → l u ≠ lam ∧ l u ≠ c) → l x < lam →
      ∃ Q, (Q = 0 ∨ (Q ∈ U ∧ lam < l Q ∧ Q < x)) ∧
        x + 2 ^ l x + (if l x < c then 2 ^ c else 0) ≤ Q + 2 ^ lam := by
  intro x
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    intro hx hfree hlx
    have hxc : l x ≠ c := (hfree x hx le_rfl).2
    have h0 := two_pow_lt hlx
    have hcl := two_pow_lt hc
    rcases h.2.2 x hx with hb | ⟨q1, hq1, hq1x, hl1, hxq⟩
    · refine ⟨0, Or.inl rfl, ?_⟩
      by_cases hi : l x < c
      · simp only [hi, ↓reduceIte]
        have h2 := two_pow_lt hi
        omega
      · simp only [hi, ↓reduceIte]
        omega
    · have h1 := two_pow_lt hl1
      have hq1f := hfree q1 hq1 (by omega)
      rcases lt_or_gt_of_ne hq1f.1 with hlt | hgt
      · obtain ⟨Q, hQ, hle⟩ := ih q1 hq1x hq1 (fun u hu hux => hfree u hu (by omega)) hlt
        refine ⟨Q, ?_, ?_⟩
        · rcases hQ with e | ⟨a, b, c'⟩
          · left
            exact e
          · right
            exact ⟨a, b, by omega⟩
        · by_cases hi : l x < c
          · simp only [hi, ↓reduceIte]
            have h2 := two_pow_lt hi
            by_cases hi1 : l q1 < c
            · simp only [hi1, ↓reduceIte] at hle
              omega
            · simp only [hi1, ↓reduceIte] at hle
              have h3 := two_pow_lt (show c < l q1 by omega)
              omega
          · simp only [hi, ↓reduceIte]
            have h4 : q1 + 2 ^ l q1 ≤ Q + 2 ^ lam := by omega
            omega
      · refine ⟨q1, Or.inr ⟨hq1, hgt, hq1x⟩, ?_⟩
        by_cases hi : l x < c
        · simp only [hi, ↓reduceIte]
          have h2 := two_pow_lt hi
          omega
        · simp only [hi, ↓reduceIte]
          omega

theorem val_F {d : ℕ} {U : Finset ℕ} {l : ℕ → ℕ} (h : Val d U l) (lam c : ℕ) (hc : c < lam)
    (x : ℕ) (hx : x ∈ U) (hfree : ∀ u ∈ U, u ≤ x → l u ≠ lam ∧ l u ≠ c) :
    ∃ Q, (Q = 0 ∨ (Q ∈ U ∧ lam < l Q ∧ Q ≤ x)) ∧ x + 1 + 2 ^ c ≤ Q + 2 ^ lam := by
  have hcl := two_pow_lt hc
  have h1 := Nat.one_le_two_pow (n := c)
  have hxf := hfree x hx le_rfl
  rcases lt_or_gt_of_ne hxf.1 with hlt | hgt
  · obtain ⟨Q, hQ, hle⟩ := val_E h lam c hc x hx hfree hlt
    refine ⟨Q, ?_, ?_⟩
    · rcases hQ with e | ⟨a, b, c'⟩
      · left
        exact e
      · right
        exact ⟨a, b, by omega⟩
    · have h2 := Nat.one_le_two_pow (n := l x)
      by_cases hi : l x < c
      · simp only [hi, ↓reduceIte] at hle
        omega
      · simp only [hi, ↓reduceIte] at hle
        have h3 := two_pow_lt (show c < l x by omega)
        omega
  · exact ⟨x, Or.inr ⟨hx, hgt, le_rfl⟩, by omega⟩

theorem exists_nxt (P : ℕ → Prop) :
    ∃ f : ℕ → ℕ, ∀ c m, P m → c < m → c < f c ∧ P (f c) ∧ f c ≤ m := by
  classical
  refine ⟨fun c => if h : ∃ L, P L ∧ c < L then Nat.find h else 0, ?_⟩
  intro c m hm hcm
  have hex : ∃ L, P L ∧ c < L := ⟨m, hm, hcm⟩
  simp only [hex, ↓reduceDIte]
  exact ⟨(Nat.find_spec hex).2, (Nat.find_spec hex).1, Nat.find_min' hex ⟨hm, hcm⟩⟩

theorem exists_shift (z : ℕ) (T : Finset ℕ) (l : ℕ → ℕ) :
    ∃ l' : ℕ → ℕ,
      (∀ y ∈ T, z < y → l y < l z →
        l y < l' y ∧ l' y ≤ l z ∧ (l' y = l z ∨ ∃ w ∈ T, z < w ∧ l w < l z ∧ l' y = l w)) ∧
      (∀ y1 ∈ T, ∀ y2 ∈ T, z < y1 → l y1 < l z → z < y2 → l y2 < l z → l y1 < l y2 →
        l' y1 < l' y2) ∧
      (∀ u ∈ T, ¬(z < u ∧ l u < l z) → l' u = l u) := by
  obtain ⟨f, hf⟩ := exists_nxt (fun L => L = l z ∨ ∃ w ∈ T, z < w ∧ l w < l z ∧ L = l w)
  refine ⟨fun y => if z < y ∧ l y < l z then f (l y) else l y, ?_, ?_, ?_⟩
  · intro y hy hzy hly
    have hc : z < y ∧ l y < l z := ⟨hzy, hly⟩
    simp only [hc, and_self, ↓reduceIte]
    obtain ⟨h1, h2, h3⟩ := hf (l y) (l z) (Or.inl rfl) hly
    exact ⟨h1, h3, h2⟩
  · intro y1 hy1 y2 hy2 a1 b1 a2 b2 hlt
    simp only [a1, b1, a2, b2, and_self, ↓reduceIte]
    have h1 := (hf (l y1) (l y2) (Or.inr ⟨y2, hy2, a2, b2, rfl⟩) hlt).2.2
    have h2 := (hf (l y2) (l z) (Or.inl rfl) b2).1
    omega
  · intro u hu hn
    simp only [hn, ↓reduceIte]

theorem erase_aux {d z : ℕ} {T : Finset ℕ} {l l' : ℕ → ℕ} (h : Val d (insert z T) l) (hz : z ∉ T)
    (hW : ∀ y ∈ T, z < y → l y < l z →
      l y < l' y ∧ l' y ≤ l z ∧ (l' y = l z ∨ ∃ w ∈ T, z < w ∧ l w < l z ∧ l' y = l w))
    {y u : ℕ} (hy : y ∈ T) (hzy : z < y) (hly : l y < l z) (hu : u ∈ T)
    (hnu : ¬(z < u ∧ l u < l z)) : l' y ≠ l u := by
  intro e
  rcases (hW y hy hzy hly).2.2 with e1 | ⟨w, hw, hzw, hlw, e2⟩
  · have e3 : u = z :=
      h.1 (Finset.mem_insert_of_mem hu) (Finset.mem_insert_self z T) (e.symm.trans e1)
    rw [e3] at hu
    exact hz hu
  · have e3 : u = w :=
      h.1 (Finset.mem_insert_of_mem hu) (Finset.mem_insert_of_mem hw) (e.symm.trans e2)
    rw [e3] at hnu
    exact hnu ⟨hzw, hlw⟩

theorem erase_inj {d z : ℕ} {T : Finset ℕ} {l l' : ℕ → ℕ} (h : Val d (insert z T) l) (hz : z ∉ T)
    (hW : ∀ y ∈ T, z < y → l y < l z →
      l y < l' y ∧ l' y ≤ l z ∧ (l' y = l z ∨ ∃ w ∈ T, z < w ∧ l w < l z ∧ l' y = l w))
    (hmono : ∀ y1 ∈ T, ∀ y2 ∈ T, z < y1 → l y1 < l z → z < y2 → l y2 < l z → l y1 < l y2 →
      l' y1 < l' y2)
    (hN : ∀ u ∈ T, ¬(z < u ∧ l u < l z) → l' u = l u) : Set.InjOn l' (T : Set ℕ) := by
  intro a ha b hb hab
  have ha' : a ∈ T := ha
  have hb' : b ∈ T := hb
  by_cases wa : z < a ∧ l a < l z <;> by_cases wb : z < b ∧ l b < l z
  · rcases lt_trichotomy (l a) (l b) with hlt | heq | hgt
    · have h1 := hmono a ha' b hb' wa.1 wa.2 wb.1 wb.2 hlt
      omega
    · exact h.1 (Finset.mem_insert_of_mem ha') (Finset.mem_insert_of_mem hb') heq
    · have h1 := hmono b hb' a ha' wb.1 wb.2 wa.1 wa.2 hgt
      omega
  · exact absurd (hab.trans (hN b hb' wb)) (erase_aux h hz hW ha' wa.1 wa.2 hb' wb)
  · exact absurd (hab.symm.trans (hN a ha' wa)) (erase_aux h hz hW hb' wb.1 wb.2 ha' wa)
  · rw [hN a ha' wa, hN b hb' wb] at hab
    exact h.1 (Finset.mem_insert_of_mem ha') (Finset.mem_insert_of_mem hb') hab

theorem erase_wit_out {d z : ℕ} {T : Finset ℕ} {l l' : ℕ → ℕ} (h : Val d (insert z T) l)
    (hW : ∀ y ∈ T, z < y → l y < l z →
      l y < l' y ∧ l' y ≤ l z ∧ (l' y = l z ∨ ∃ w ∈ T, z < w ∧ l w < l z ∧ l' y = l w))
    (hN : ∀ u ∈ T, ¬(z < u ∧ l u < l z) → l' u = l u)
    {u : ℕ} (hu : u ∈ T) (hnu : ¬(z < u ∧ l u < l z)) :
    u ≤ 2 ^ l' u ∨ ∃ q ∈ T, q < u ∧ l' u < l' q ∧ u ≤ q + 2 ^ l' u := by
  have hge : ∀ q ∈ T, l q ≤ l' q := by
    intro q hq
    by_cases wq : z < q ∧ l q < l z
    · exact (hW q hq wq.1 wq.2).1.le
    · exact (hN q hq wq).ge
  rw [hN u hu hnu]
  rcases h.2.2 u (Finset.mem_insert_of_mem hu) with hb | ⟨q, hq, hqu, hlq, hle⟩
  · left
    exact hb
  · rcases Finset.mem_insert.mp hq with e | hqT
    · rw [e] at hqu hlq
      exact absurd ⟨hqu, hlq⟩ hnu
    · right
      exact ⟨q, hqT, hqu, lt_of_lt_of_le hlq (hge q hqT), hle⟩

theorem erase_wit_low {d z : ℕ} {T : Finset ℕ} {l l' : ℕ → ℕ} (h : Val d (insert z T) l)
    (hz : z ∉ T) (hen : z = 1 ∨ ∃ x ∈ T, z = x + 1)
    (hW : ∀ y ∈ T, z < y → l y < l z →
      l y < l' y ∧ l' y ≤ l z ∧ (l' y = l z ∨ ∃ w ∈ T, z < w ∧ l w < l z ∧ l' y = l w))
    (hN : ∀ u ∈ T, ¬(z < u ∧ l u < l z) → l' u = l u)
    {y : ℕ} (hy : y ∈ T) (hzy : z < y) (hly : l y < l z) (hyz : y ≤ z + 2 ^ l y) :
    y ≤ 2 ^ l' y ∨ ∃ q ∈ T, q < y ∧ l' y < l' q ∧ y ≤ q + 2 ^ l' y := by
  obtain ⟨hlt, hle, -⟩ := hW y hy hzy hly
  have hp := two_pow_lt hlt
  have h1 := Nat.one_le_two_pow (n := l y)
  rcases hen with rfl | ⟨x, hx, rfl⟩
  · left
    omega
  · have hfree : ∀ u ∈ insert (x + 1) T, u ≤ x → l u ≠ l' y ∧ l u ≠ l y := by
      intro u hu hux
      have huT : u ∈ T := by
        rcases Finset.mem_insert.mp hu with e | huT
        · omega
        · exact huT
      refine ⟨fun e => erase_aux h hz hW hy hzy hly huT (fun w => by omega) e.symm, fun e => ?_⟩
      have e3 : u = y := h.1 hu (Finset.mem_insert_of_mem hy) e
      omega
    obtain ⟨Q, hQ, hQle⟩ := val_F h (l' y) (l y) hlt x (Finset.mem_insert_of_mem hx) hfree
    rcases hQ with e | ⟨hQU, hQl, hQx⟩
    · left
      omega
    · have hQT : Q ∈ T := by
        rcases Finset.mem_insert.mp hQU with e | hQT
        · omega
        · exact hQT
      right
      refine ⟨Q, hQT, by omega, ?_, by omega⟩
      rw [hN Q hQT (fun w => by omega)]
      exact hQl

theorem erase_wit_in {d z : ℕ} {T : Finset ℕ} {l l' : ℕ → ℕ} (h : Val d (insert z T) l)
    (hz : z ∉ T) (hen : z = 1 ∨ ∃ x ∈ T, z = x + 1)
    (hW : ∀ y ∈ T, z < y → l y < l z →
      l y < l' y ∧ l' y ≤ l z ∧ (l' y = l z ∨ ∃ w ∈ T, z < w ∧ l w < l z ∧ l' y = l w))
    (hmono : ∀ y1 ∈ T, ∀ y2 ∈ T, z < y1 → l y1 < l z → z < y2 → l y2 < l z → l y1 < l y2 →
      l' y1 < l' y2)
    (hN : ∀ u ∈ T, ¬(z < u ∧ l u < l z) → l' u = l u)
    {y : ℕ} (hy : y ∈ T) (hzy : z < y) (hly : l y < l z) :
    y ≤ 2 ^ l' y ∨ ∃ q ∈ T, q < y ∧ l' y < l' q ∧ y ≤ q + 2 ^ l' y := by
  obtain ⟨hlt, hle, -⟩ := hW y hy hzy hly
  have hp := two_pow_lt hlt
  have h1 := Nat.one_le_two_pow (n := l y)
  rcases h.2.2 y (Finset.mem_insert_of_mem hy) with hb | ⟨q, hq, hqy, hlq, hyq⟩
  · left
    omega
  · by_cases hzq : z < q
    · have hqT : q ∈ T := by
        rcases Finset.mem_insert.mp hq with e | hqT
        · omega
        · exact hqT
      right
      refine ⟨q, hqT, hqy, ?_, by omega⟩
      by_cases wq : l q < l z
      · exact hmono y hy q hqT hzy hly hzq wq hlq
      · rw [hN q hqT (fun w => wq w.2)]
        have hne : l q ≠ l z := by
          intro e
          have e3 : q = z := h.1 hq (Finset.mem_insert_self z T) e
          omega
        omega
    · exact erase_wit_low h hz hen hW hN hy hzy hly (by omega)

theorem erase_core {d z : ℕ} {T : Finset ℕ} {l l' : ℕ → ℕ} (h : Val d (insert z T) l)
    (hz : z ∉ T) (hen : z = 1 ∨ ∃ x ∈ T, z = x + 1)
    (hW : ∀ y ∈ T, z < y → l y < l z →
      l y < l' y ∧ l' y ≤ l z ∧ (l' y = l z ∨ ∃ w ∈ T, z < w ∧ l w < l z ∧ l' y = l w))
    (hmono : ∀ y1 ∈ T, ∀ y2 ∈ T, z < y1 → l y1 < l z → z < y2 → l y2 < l z → l y1 < l y2 →
      l' y1 < l' y2)
    (hN : ∀ u ∈ T, ¬(z < u ∧ l u < l z) → l' u = l u) : Val d T l' := by
  refine ⟨erase_inj h hz hW hmono hN, ?_, ?_⟩
  · intro y hy
    have hzd := h.2.1 z (Finset.mem_insert_self z T)
    by_cases wy : z < y ∧ l y < l z
    · have h1 := (hW y hy wy.1 wy.2).2.1
      omega
    · rw [hN y hy wy]
      exact h.2.1 y (Finset.mem_insert_of_mem hy)
  · intro y hy
    by_cases wy : z < y ∧ l y < l z
    · exact erase_wit_in h hz hen hW hmono hN hy wy.1 wy.2
    · exact erase_wit_out h hW hN hy wy

theorem good_erase {d : ℕ} {T : Finset ℕ} {p : ℕ} (h : Good d (insert p T)) (hp : p ∉ T)
    (hen : p = 1 ∨ ∃ x ∈ T, p = x + 1) : Good d T := by
  obtain ⟨l, h⟩ := h
  obtain ⟨l', hW, hmono, hN⟩ := exists_shift p T l
  exact ⟨l', erase_core h hp hen hW hmono hN⟩

def Mv (d M : ℕ) (A B : Finset ℕ) : Prop :=
  B.card ≤ d ∧ ∃ p, p ∉ A ∧ B = insert p A ∧ 1 ≤ p ∧ p ≤ M ∧ (p = 1 ∨ ∃ x ∈ A, p = x + 1)

def Rch (d M : ℕ) : Finset ℕ → Finset ℕ → Prop :=
  Relation.ReflTransGen (fun A B => Mv d M A B ∨ Mv d M B A)

theorem rch_trans {d M : ℕ} {A B C : Finset ℕ} (h1 : Rch d M A B) (h2 : Rch d M B C) :
    Rch d M A C :=
  Relation.ReflTransGen.trans h1 h2

theorem rch_symm {d M : ℕ} {A B : Finset ℕ} (h : Rch d M A B) : Rch d M B A := by
  unfold Rch at h ⊢
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head hbc.symm ih

theorem rch_add {d M : ℕ} {S : Finset ℕ} {p : ℕ} (hp : p ∉ S) (h1 : 1 ≤ p) (hM : p ≤ M)
    (hpre : p = 1 ∨ ∃ x ∈ S, p = x + 1) (hc : S.card + 1 ≤ d) : Rch d M S (insert p S) := by
  refine Relation.ReflTransGen.single (Or.inl ⟨?_, p, hp, rfl, h1, hM, hpre⟩)
  rw [Finset.card_insert_of_notMem hp]
  exact hc

theorem jump (d M : ℕ) : ∀ (k : ℕ) (S : Finset ℕ) (x : ℕ), (x = 0 ∨ x ∈ S) →
    (∀ y ∈ S, x < y → y ≤ x + 2 ^ k → False) → S.card + (k + 1) ≤ d → x + 2 ^ k ≤ M →
    Rch d M S (insert (x + 2 ^ k) S) := by
  intro k
  induction k with
  | zero =>
    intro S x hx hfree hc hM
    have h0 : 2 ^ 0 = 1 := pow_zero 2
    rw [h0] at hfree hM ⊢
    apply rch_add
    · intro hmem
      exact hfree _ hmem (by omega) le_rfl
    · omega
    · exact hM
    · rcases hx with rfl | hx
      · left
        rfl
      · right
        exact ⟨x, hx, rfl⟩
    · omega
  | succ k ih =>
    intro S x hx hfree hc hM
    have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [pow_succ]; omega
    have hpos : 0 < 2 ^ k := by positivity
    rw [hpow] at hfree hM ⊢
    have hfreeS : ∀ y ∈ S, x < y → y ≤ x + 2 ^ k → False :=
      fun y hy h1 h2 => hfree y hy h1 (by omega)
    have hnot1 : x + 2 ^ k ∉ S := fun hm => hfree _ hm (by omega) (by omega)
    have hnot2 : x + (2 ^ k + 2 ^ k) ∉ S := fun hm => hfree _ hm (by omega) le_rfl
    have s1 : Rch d M S (insert (x + 2 ^ k) S) := ih S x hx hfreeS (by omega) (by omega)
    have s2 : Rch d M (insert (x + 2 ^ k) S)
        (insert (x + 2 ^ k + 2 ^ k) (insert (x + 2 ^ k) S)) := by
      apply ih
      · right
        exact Finset.mem_insert_self _ _
      · intro y hy h1 h2
        rcases Finset.mem_insert.mp hy with rfl | hy
        · omega
        · exact hfree y hy (by omega) (by omega)
      · rw [Finset.card_insert_of_notMem hnot1]
        omega
      · omega
    have s3 : Rch d M (insert (x + (2 ^ k + 2 ^ k)) S)
        (insert (x + 2 ^ k) (insert (x + (2 ^ k + 2 ^ k)) S)) := by
      apply ih
      · rcases hx with h | h
        · left
          exact h
        · right
          exact Finset.mem_insert_of_mem h
      · intro y hy h1 h2
        rcases Finset.mem_insert.mp hy with rfl | hy
        · omega
        · exact hfree y hy h1 (by omega)
      · rw [Finset.card_insert_of_notMem hnot2]
        omega
      · omega
    have e : insert (x + 2 ^ k + 2 ^ k) (insert (x + 2 ^ k) S)
        = insert (x + 2 ^ k) (insert (x + (2 ^ k + 2 ^ k)) S) := by
      rw [Finset.insert_comm, add_assoc]
    rw [e] at s2
    exact rch_trans s1 (rch_trans s2 (rch_symm s3))

theorem reach (d M : ℕ) : ∀ (k : ℕ) (S : Finset ℕ) (x r : ℕ), (x = 0 ∨ x ∈ S) → 1 ≤ r →
    r + 1 ≤ 2 ^ k → (∀ y ∈ S, x < y → y ≤ x + r → False) → S.card + k ≤ d → x + r ≤ M →
    ∃ P : Finset ℕ, (∀ y ∈ P, x < y ∧ y ≤ x + r) ∧ x + r ∈ P ∧ P.card ≤ k ∧
      (r + 2 ≤ 2 ^ k → P.card + 1 ≤ k) ∧ Rch d M S (S ∪ P) := by
  intro k
  induction k with
  | zero =>
    intro S x r hx h1 h2
    have h0 : 2 ^ 0 = 1 := pow_zero 2
    omega
  | succ k ih =>
    intro S x r hx h1 h2 hfree hc hM
    have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [pow_succ]; omega
    have hpos : 0 < 2 ^ k := by positivity
    rw [hpow] at h2 ⊢
    rcases lt_trichotomy r (2 ^ k) with hlt | heq | hgt
    · obtain ⟨P, hP1, hP2, hP3, hP4, hP5⟩ := ih S x r hx h1 (by omega) hfree (by omega) hM
      exact ⟨P, hP1, hP2, by omega, fun _ => by omega, hP5⟩
    · subst heq
      refine ⟨{x + 2 ^ k}, ?_, Finset.mem_singleton_self _, ?_, ?_, ?_⟩
      · intro y hy
        rw [Finset.mem_singleton] at hy
        omega
      · rw [Finset.card_singleton]
        omega
      · intro h
        have hk : k ≠ 0 := by
          rintro rfl
          simp at h
        rw [Finset.card_singleton]
        omega
      · rw [Finset.union_singleton]
        exact jump d M k S x hx hfree (by omega) hM
    · obtain ⟨r', rfl⟩ : ∃ r', r = 2 ^ k + r' := ⟨r - 2 ^ k, by omega⟩
      have hnot1 : x + 2 ^ k ∉ S := fun hm => hfree _ hm (by omega) (by omega)
      have s1 : Rch d M S (insert (x + 2 ^ k) S) :=
        jump d M k S x hx (fun y hy a b => hfree y hy a (by omega)) (by omega) (by omega)
      have hfree1 : ∀ y ∈ insert (x + 2 ^ k) S, x + 2 ^ k < y → y ≤ x + 2 ^ k + r' → False := by
        intro y hy a b
        rcases Finset.mem_insert.mp hy with rfl | hy
        · omega
        · exact hfree y hy (by omega) (by omega)
      have hc1 : (insert (x + 2 ^ k) S).card + k ≤ d := by
        rw [Finset.card_insert_of_notMem hnot1]
        omega
      obtain ⟨P, hP1, hP2, hP3, hP4, hP5⟩ := ih (insert (x + 2 ^ k) S) (x + 2 ^ k) r'
        (Or.inr (Finset.mem_insert_self _ _)) (by omega) (by omega) hfree1 hc1 (by omega)
      have hcard := Finset.card_insert_le (x + 2 ^ k) P
      refine ⟨insert (x + 2 ^ k) P, ?_, ?_, ?_, ?_, ?_⟩
      · intro y hy
        rcases Finset.mem_insert.mp hy with rfl | hy
        · omega
        · have := hP1 y hy
          omega
      · apply Finset.mem_insert_of_mem
        have e : x + (2 ^ k + r') = x + 2 ^ k + r' := by omega
        rw [e]
        exact hP2
      · omega
      · intro h
        have := hP4 (by omega)
        omega
      · rw [Finset.union_insert, ← Finset.insert_union]
        exact rch_trans s1 hP5

theorem strat (d n : ℕ) (hn : 2 ≤ n) (h : n + 2 < 2 ^ d) :
    ∃ S : Finset ℕ, n + 1 ∈ S ∧ S.card < d ∧ (∀ p ∈ S, 2 ≤ p ∧ p ≤ n + 1) ∧ Rch d (n + 1) ∅ S := by
  obtain ⟨P, hP1, hP2, hP3, hP4, hP5⟩ := reach d (n + 1) d ∅ 0 (n + 1) (Or.inl rfl) (by omega)
    (by omega) (by simp) (by simp) (by omega)
  rw [Finset.empty_union] at hP5
  rw [zero_add] at hP2
  have hc := hP4 (by omega)
  refine ⟨P.erase 1, ?_, ?_, ?_, ?_⟩
  · exact Finset.mem_erase.mpr ⟨by omega, hP2⟩
  · have := Finset.card_erase_le (s := P) (a := 1)
    omega
  · intro p hp
    obtain ⟨hne, hp⟩ := Finset.mem_erase.mp hp
    have := hP1 p hp
    omega
  · by_cases h1 : 1 ∈ P
    · exact rch_trans hP5 (Relation.ReflTransGen.single (Or.inr ⟨by omega, 1,
        Finset.notMem_erase 1 P, (Finset.insert_erase h1).symm, le_rfl, by omega, Or.inl rfl⟩))
    · rw [Finset.erase_eq_of_notMem h1]
      exact hP5

theorem strat_two (d : ℕ) (hd : 2 ≤ d) : Rch d 3 ∅ {2, 3} := by
  have a1 : Rch d 3 ∅ (insert 1 ∅) :=
    rch_add (by simp) le_rfl (by omega) (Or.inl rfl) (by simp; omega)
  have a2 : Rch d 3 (insert 1 ∅) (insert 2 (insert 1 ∅)) :=
    rch_add (by decide) (by omega) (by omega) (Or.inr ⟨1, by simp, rfl⟩) (by simp; omega)
  have a3 : Rch d 3 (insert 2 ∅) (insert 1 (insert 2 ∅)) :=
    rch_add (by decide) le_rfl (by omega) (Or.inl rfl) (by simp; omega)
  have a4 : Rch d 3 (insert 2 ∅) (insert 3 (insert 2 ∅)) :=
    rch_add (by decide) (by omega) le_rfl (Or.inr ⟨2, by simp, rfl⟩) (by simp; omega)
  have e1 : (insert 2 (insert 1 ∅) : Finset ℕ) = insert 1 (insert 2 ∅) := by decide
  have e2 : (insert 3 (insert 2 ∅) : Finset ℕ) = {2, 3} := by decide
  rw [e1] at a2
  rw [e2] at a4
  exact rch_trans a1 (rch_trans a2 (rch_trans (rch_symm a3) a4))

open MvPolynomial PEqualNP.ProofComplexity

abbrev Poly (n : ℕ) := MvPolynomial (Fin n) (ZMod 2)

theorem zmod2_add_self (c : ZMod 2) : c + c = 0 := by
  fin_cases c <;> decide

theorem add_self_eq_zero {n : ℕ} (p : Poly n) : p + p = 0 := by
  ext d
  rw [AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_zero]
  exact zmod2_add_self (p.coeff d)

theorem zmod2_eq_one_of_ne_zero {c : ZMod 2} (h : c ≠ 0) : c = 1 := by
  fin_cases c
  · exact absurd rfl h
  · rfl

theorem coeff_add' {n : ℕ} (p q : Poly n) (d : Fin n →₀ ℕ) :
    (p + q).coeff d = p.coeff d + q.coeff d := by
  rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply]

noncomputable def indF {n : ℕ} (S : Finset (Fin n)) : Fin n →₀ ℕ :=
  ∑ i ∈ S, Finsupp.single i 1

theorem indF_apply {n : ℕ} (S : Finset (Fin n)) (i : Fin n) :
    indF S i = if i ∈ S then 1 else 0 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [indF]
  | @insert j S hj ih =>
    unfold indF
    rw [Finset.sum_insert hj, Finsupp.add_apply, Finsupp.single_apply]
    change (if j = i then 1 else 0) + indF S i = if i ∈ insert j S then 1 else 0
    rw [ih]
    by_cases hji : j = i
    · subst hji
      simp [hj]
    · have hij : i ≠ j := Ne.symm hji
      simp [hji, hij]

theorem indF_support {n : ℕ} (S : Finset (Fin n)) : (indF S).support = S := by
  ext i
  rw [Finsupp.mem_support_iff, indF_apply]
  by_cases hi : i ∈ S <;> simp [hi]

theorem indF_sum {n : ℕ} (S : Finset (Fin n)) : (indF S).sum (fun _ k => k) = S.card := by
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
  simp only [indF_apply, Finset.sum_boole, Nat.cast_id]
  congr 1
  ext i
  simp

theorem indF_inj {n : ℕ} {S T : Finset (Fin n)} (h : indF S = indF T) : S = T := by
  rw [← indF_support S, ← indF_support T, h]

noncomputable def mon {n : ℕ} (S : Finset (Fin n)) : Poly n :=
  ∏ i ∈ S, X i

theorem mon_eq_monomial {n : ℕ} (S : Finset (Fin n)) : mon S = monomial (indF S) 1 := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp [mon, indF, monomial_zero']
  | @insert i S hi ih =>
    rw [mon, Finset.prod_insert hi, ← mon, ih, X, monomial_mul_monomial, mul_one]
    congr 1
    unfold indF
    rw [Finset.sum_insert hi]

theorem totalDegree_mon_le {n : ℕ} (S : Finset (Fin n)) : (mon S).totalDegree ≤ S.card := by
  rw [mon_eq_monomial]
  refine (totalDegree_monomial_le (indF S) (1 : ZMod 2)).trans ?_
  change (indF S).sum (fun _ k => k) ≤ S.card
  rw [indF_sum]

theorem mon_mul_disjoint {n : ℕ} {S T : Finset (Fin n)} (h : Disjoint S T) :
    mon S * mon T = mon (S ∪ T) := by
  unfold mon
  rw [Finset.prod_union h]

theorem coeff_mon {n : ℕ} (S T : Finset (Fin n)) :
    (mon S).coeff (indF T) = if S = T then 1 else 0 := by
  rw [mon_eq_monomial, coeff_monomial]
  by_cases h : S = T
  · subst h; simp
  · have hne : indF S ≠ indF T := fun e => h (indF_inj e)
    simp [h, hne]

noncomputable def ml {n : ℕ} (d : Fin n →₀ ℕ) : Fin n →₀ ℕ :=
  d.mapRange (fun k => min k 1) rfl

theorem ml_eq_indF_support {n : ℕ} (d : Fin n →₀ ℕ) : ml d = indF d.support := by
  ext i
  rw [ml, Finsupp.mapRange_apply, indF_apply]
  by_cases h : d i = 0
  · have hns : i ∉ d.support := Finsupp.notMem_support_iff.mpr h
    simp [h, hns]
  · have hs : i ∈ d.support := Finsupp.mem_support_iff.mpr h
    simp only [hs, ite_true]
    omega

noncomputable def nf {n : ℕ} (p : Poly n) : Poly n :=
  ∑ d ∈ p.support, monomial (ml d) (p.coeff d)

theorem nf_eq_sum_indF {n : ℕ} (p : Poly n) :
    nf p = ∑ d ∈ p.support, monomial (indF d.support) (p.coeff d) := by
  unfold nf
  refine Finset.sum_congr rfl fun d _ => by rw [ml_eq_indF_support]

theorem nf_monomial {n : ℕ} (d : Fin n →₀ ℕ) (c : ZMod 2) :
    nf (monomial d c) = monomial (indF d.support) c := by
  by_cases hc : c = 0
  · subst hc
    simp [nf]
  · rw [nf_eq_sum_indF, support_monomial, ite_eq_right_of_eq_false _ _ (eq_false hc),
      Finset.sum_singleton, coeff_monomial, ite_eq_left_of_eq_true _ _ (eq_true rfl)]

theorem nf_add {n : ℕ} (p q : Poly n) : nf (p + q) = nf p + nf q := by
  classical
  have aux : ∀ (s : Finset (Fin n →₀ ℕ)) (r : Poly n), r.support ⊆ s →
      nf r = ∑ d ∈ s, monomial (indF d.support) (r.coeff d) := by
    intro s r hs
    rw [nf_eq_sum_indF]
    apply Finset.sum_subset hs
    intro d _ hd
    have h0 : r.coeff d = 0 := notMem_support_iff.mp hd
    rw [h0, map_zero]
  let s := p.support ∪ q.support
  have hpq : (p + q).support ⊆ s := support_add
  rw [aux s (p + q) hpq, aux s p Finset.subset_union_left, aux s q Finset.subset_union_right,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [coeff_add', map_add]

theorem nf_zero {n : ℕ} : nf (0 : Poly n) = 0 := by
  simp [nf]

theorem nf_sum {n : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Poly n) :
    nf (∑ a ∈ s, f a) = ∑ a ∈ s, nf (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [nf_zero]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, nf_add, ih]

theorem nf_mul_monomial {n : ℕ} (d1 d2 : Fin n →₀ ℕ) (c1 c2 : ZMod 2) :
    nf (monomial d1 c1 * monomial d2 c2) = monomial (indF (d1.support ∪ d2.support)) (c1 * c2) := by
  rw [monomial_mul_monomial, nf_monomial]
  apply congrArg (fun s => monomial (indF s) (c1 * c2))
  ext i
  rw [Finset.mem_union, Finsupp.mem_support_iff, Finsupp.mem_support_iff,
    Finsupp.mem_support_iff, Finsupp.add_apply]
  omega

theorem nf_mul_boolAx {n : ℕ} (p : Poly n) (v : Fin n) :
    nf (p * (X v * X v + X v)) = 0 := by
  rw [p.as_sum, Finset.sum_mul, nf_sum]
  apply Finset.sum_eq_zero
  intro d _
  rw [mul_add, nf_add]
  have h1 : (X v : Poly n) * X v = monomial (Finsupp.single v 2) 1 := by
    rw [X, monomial_mul_monomial, mul_one, ← Finsupp.single_add]
  have h2 : (X v : Poly n) = monomial (Finsupp.single v 1) 1 := rfl
  rw [h1, h2, nf_mul_monomial, nf_mul_monomial]
  have hsupp : (Finsupp.single v 2).support = (Finsupp.single v 1).support := by
    ext i
    simp
  rw [hsupp, add_self_eq_zero]

theorem nf_monomial_mul_mon {n : ℕ} (d : Fin n →₀ ℕ) (S : Finset (Fin n)) :
    nf (monomial d (1 : ZMod 2) * mon S) = mon (d.support ∪ S) := by
  rw [mon_eq_monomial, nf_mul_monomial, mul_one, indF_support, mon_eq_monomial]

theorem card_support_le_sum {n : ℕ} (d : Fin n →₀ ℕ) : d.support.card ≤ d.sum (fun _ k => k) := by
  rw [Finsupp.sum]
  calc d.support.card = ∑ _i ∈ d.support, 1 := by simp
    _ ≤ ∑ i ∈ d.support, d i := by
      refine Finset.sum_le_sum fun i hi => ?_
      have hne : d i ≠ 0 := Finsupp.mem_support_iff.mp hi
      omega

theorem totalDegree_X_le_one {n : ℕ} (j : Fin n) : (X j : Poly n).totalDegree ≤ 1 := by
  rw [X]
  exact (totalDegree_monomial_le (Finsupp.single j 1) (1 : ZMod 2)).trans (by simp)

theorem totalDegree_clausePoly_le {n : ℕ} (C : Clause (Fin n)) :
    (clausePoly C).totalDegree ≤ C.card := by
  classical
  induction C using Finset.induction_on with
  | empty => simp [clausePoly]
  | @insert l C hl ih =>
    rw [clausePoly, Finset.prod_insert hl, Finset.card_insert_of_notMem hl]
    have h1 := totalDegree_mul (if l.2 = true then 1 + X l.1 else X l.1 : Poly n) (clausePoly C)
    have h2 : (if l.2 = true then 1 + X l.1 else X l.1 : Poly n).totalDegree ≤ 1 := by
      cases l.2
      · simp only [Bool.false_eq_true, ite_false]; exact totalDegree_X_le_one l.1
      · simp only [ite_true]
        exact (totalDegree_add (1 : Poly n) (X l.1)).trans (max_le (by simp) (totalDegree_X_le_one l.1))
    rw [clausePoly] at h1 ih
    omega

def clauseOf {n : ℕ} (pred : Fin n → Finset (Fin n)) (v : Fin n) : Clause (Fin n) :=
  insert (v, true) ((pred v).image (fun u => (u, false)))

theorem clausePoly_clauseOf {n : ℕ} (pred : Fin n → Finset (Fin n)) (v : Fin n)
    (hv : v ∉ pred v) :
    clausePoly (clauseOf pred v) = mon (pred v) + mon (insert v (pred v)) := by
  classical
  unfold clausePoly clauseOf
  have hni : (v, true) ∉ (pred v).image (fun u => (u, false)) := by
    rw [Finset.mem_image]
    rintro ⟨u, _, hu⟩
    have := (Prod.mk.inj hu).2
    simp at this
  rw [Finset.prod_insert hni]
  simp only [ite_true]
  have himg : ∏ l ∈ (pred v).image (fun u => (u, false)),
      (if l.2 = true then (1 : Poly n) + X l.1 else X l.1) = mon (pred v) := by
    rw [Finset.prod_image (fun a _ b _ h => (Prod.mk.inj h).1)]
    unfold mon
    refine Finset.prod_congr rfl fun u _ => by simp
  rw [himg, add_mul, one_mul]
  congr 1
  unfold mon
  rw [Finset.prod_insert hv]

theorem totalDegree_clauseOf {n : ℕ} (pred : Fin n → Finset (Fin n)) (v : Fin n)
    (hv : v ∉ pred v) :
    (clausePoly (clauseOf pred v)).totalDegree = (pred v).card + 1 := by
  apply le_antisymm
  · have h1 := totalDegree_clausePoly_le (clauseOf pred v)
    have h2 : (clauseOf pred v).card ≤ (pred v).card + 1 := by
      unfold clauseOf
      exact (Finset.card_insert_le _ _).trans (Nat.add_le_add_right Finset.card_image_le 1)
    omega
  · rw [clausePoly_clauseOf pred v hv]
    have hmem : indF (insert v (pred v)) ∈ (mon (pred v) + mon (insert v (pred v))).support := by
      rw [mem_support_iff, coeff_add', coeff_mon, coeff_mon]
      have hne : pred v ≠ insert v (pred v) := by
        intro h
        apply hv
        rw [h]
        exact Finset.mem_insert_self v _
      simp [hne]
    have hle : (indF (insert v (pred v))).sum (fun _ k => k) ≤
        (mon (pred v) + mon (insert v (pred v))).totalDegree :=
      Finset.le_sup (f := fun s : Fin n →₀ ℕ => s.sum (fun _ k => k)) hmem
    rw [indF_sum, Finset.card_insert_of_notMem hv] at hle
    exact hle

def pin1 {n : ℕ} (s t : Fin n) : Clause (Fin n) := {(t, true), (s, true)}
def pin2 {n : ℕ} (s t : Fin n) : Clause (Fin n) := {(t, false), (s, true)}
def pin3 {n : ℕ} (s t : Fin n) : Clause (Fin n) := {(t, false), (s, false)}

theorem clausePoly_pin1 {n : ℕ} {s t : Fin n} (hst : s ≠ t) :
    clausePoly (pin1 s t) = (1 + X s) + X t + X t * X s := by
  unfold clausePoly pin1
  have hne : (t, true) ≠ (s, true) := fun h => hst (Prod.mk.inj h).1.symm
  rw [Finset.prod_pair hne]
  simp only [ite_true]
  ring

theorem clausePoly_pin2 {n : ℕ} {s t : Fin n} :
    clausePoly (pin2 s t) = X t + X t * X s := by
  unfold clausePoly pin2
  have hne : (t, false) ≠ (s, true) := fun h => by have := (Prod.mk.inj h).2; simp at this
  rw [Finset.prod_pair hne]
  simp only [Bool.false_eq_true, ite_false, ite_true]
  ring

theorem clausePoly_pin3 {n : ℕ} {s t : Fin n} (hst : s ≠ t) :
    clausePoly (pin3 s t) = X t * X s := by
  unfold clausePoly pin3
  have hne : (t, false) ≠ (s, false) := fun h => hst (Prod.mk.inj h).1.symm
  rw [Finset.prod_pair hne]
  simp only [Bool.false_eq_true, ite_false]

theorem totalDegree_pin1 {n : ℕ} {s t : Fin n} (hst : s ≠ t) :
    (clausePoly (pin1 s t)).totalDegree = 2 := by
  apply le_antisymm
  · exact (totalDegree_clausePoly_le _).trans (by unfold pin1; exact Finset.card_le_two)
  · rw [clausePoly_pin1 hst]
    have hts : t ≠ s := hst.symm
    have heq : (1 + X s + X t + X t * X s : Poly n) =
        mon ∅ + mon {s} + mon {t} + mon {t, s} := by
      simp [mon, Finset.prod_pair hts]
    rw [heq]
    have hmem : indF ({t, s} : Finset (Fin n)) ∈
        (mon ∅ + mon {s} + mon {t} + mon {t, s}).support := by
      rw [mem_support_iff, coeff_add', coeff_add', coeff_add', coeff_mon, coeff_mon, coeff_mon, coeff_mon]
      have h1 : (∅ : Finset (Fin n)) ≠ {t, s} := (Finset.insert_ne_empty _ _).symm
      have h2 : ({s} : Finset (Fin n)) ≠ {t, s} := by
        intro h
        have : t ∈ ({s} : Finset (Fin n)) := by rw [h]; simp
        exact hts (Finset.mem_singleton.mp this)
      have h3 : ({t} : Finset (Fin n)) ≠ {t, s} := by
        intro h
        have : s ∈ ({t} : Finset (Fin n)) := by rw [h]; simp
        exact hst (Finset.mem_singleton.mp this)
      simp [h1, h2, h3]
    have hle := Finset.le_sup (f := fun e : Fin n →₀ ℕ => e.sum (fun _ k => k)) hmem
    rw [indF_sum, Finset.card_pair hts] at hle
    exact hle

theorem totalDegree_pin2 {n : ℕ} {s t : Fin n} (hst : s ≠ t) :
    (clausePoly (pin2 s t)).totalDegree = 2 := by
  apply le_antisymm
  · exact (totalDegree_clausePoly_le _).trans (by unfold pin2; exact Finset.card_le_two)
  · rw [clausePoly_pin2]
    have hts : t ≠ s := hst.symm
    have heq : (X t + X t * X s : Poly n) = mon {t} + mon {t, s} := by
      simp [mon, Finset.prod_pair hts]
    rw [heq]
    have hmem : indF ({t, s} : Finset (Fin n)) ∈ (mon {t} + mon {t, s}).support := by
      rw [mem_support_iff, coeff_add', coeff_mon, coeff_mon]
      have h3 : ({t} : Finset (Fin n)) ≠ {t, s} := by
        intro h
        have : s ∈ ({t} : Finset (Fin n)) := by rw [h]; simp
        exact hst (Finset.mem_singleton.mp this)
      simp [h3]
    have hle := Finset.le_sup (f := fun e : Fin n →₀ ℕ => e.sum (fun _ k => k)) hmem
    rw [indF_sum, Finset.card_pair hts] at hle
    exact hle

theorem totalDegree_pin3 {n : ℕ} {s t : Fin n} (hst : s ≠ t) :
    (clausePoly (pin3 s t)).totalDegree = 2 := by
  apply le_antisymm
  · exact (totalDegree_clausePoly_le _).trans (by unfold pin3; exact Finset.card_le_two)
  · rw [clausePoly_pin3 hst]
    have hts : t ≠ s := hst.symm
    have heq : (X t * X s : Poly n) = mon {t, s} := by
      simp [mon, Finset.prod_pair hts]
    rw [heq]
    have hmem : indF ({t, s} : Finset (Fin n)) ∈ (mon {t, s}).support := by
      rw [mem_support_iff, coeff_mon]
      simp
    have hle := Finset.le_sup (f := fun e : Fin n →₀ ℕ => e.sum (fun _ k => k)) hmem
    rw [indF_sum, Finset.card_pair hts] at hle
    exact hle

def enabled {n : ℕ} (s : Fin n) (pred : Fin n → Finset (Fin n))
    (z : Option (Fin n)) (current : Finset (Option (Fin n))) : Prop :=
  z = none ∨ ∃ i : Fin n, z = some i ∧
    ((i = s ∧ none ∈ current) ∨ (i ≠ s ∧ ∀ u ∈ pred i, some u ∈ current))

def up {n : ℕ} (d : ℕ) (s : Fin n) (pred : Fin n → Finset (Fin n))
    (A B : Finset (Option (Fin n))) : Prop :=
  B.card ≤ d ∧ ∃ z, z ∉ A ∧ B = insert z A ∧ enabled s pred z A

def stepRel {n : ℕ} (d : ℕ) (s : Fin n) (pred : Fin n → Finset (Fin n))
    (U V : Finset (Option (Fin n))) : Prop :=
  up d s pred U V ∨ up d s pred V U

theorem stepRel_symm {n : ℕ} {d : ℕ} {s : Fin n} {pred : Fin n → Finset (Fin n)}
    {U V : Finset (Option (Fin n))} (h : stepRel d s pred U V) : stepRel d s pred V U :=
  h.symm

theorem rtg_symm {n : ℕ} {d : ℕ} {s : Fin n} {pred : Fin n → Finset (Fin n)}
    {U V : Finset (Option (Fin n))}
    (h : Relation.ReflTransGen (stepRel d s pred) U V) :
    Relation.ReflTransGen (stepRel d s pred) V U := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact Relation.ReflTransGen.head (stepRel_symm hstep) ih

theorem bridge_source {n : ℕ} {d : ℕ} {s : Fin n} {pred : Fin n → Finset (Fin n)}
    (M : Finset (Fin n)) (hns : s ∉ M) (hcard : M.card + 2 ≤ d) :
    Relation.ReflTransGen (stepRel d s pred) (M.image some) ((insert s M).image some) := by
  let A0 := M.image some
  let A1 := insert none A0
  let A2 := insert (some s) A1
  let B0 := (insert s M).image some
  have hnone0 : none ∉ A0 := by
    simp only [A0, Finset.mem_image, reduceCtorEq, and_false, exists_false, not_false_eq_true]
  have hs1 : some s ∉ A1 := by
    simp only [A1, A0, Finset.mem_insert, Finset.mem_image, Option.some.injEq, reduceCtorEq,
      false_or, not_exists, not_and]
    intro x hx hxs
    exact hns (hxs ▸ hx)
  have hnoneB : none ∉ B0 := by
    simp only [B0, Finset.mem_image, reduceCtorEq, and_false, exists_false, not_false_eq_true]
  have hA0c : A0.card = M.card := Finset.card_image_of_injective M (Option.some_injective (Fin n))
  have hA1c : A1.card = M.card + 1 := by rw [Finset.card_insert_of_notMem hnone0, hA0c]
  have hA2c : A2.card = M.card + 2 := by rw [Finset.card_insert_of_notMem hs1, hA1c]
  have hA2eq : A2 = insert none B0 := by
    ext z
    simp only [A2, A1, A0, B0, Finset.mem_insert, Finset.mem_image]
    constructor
    · rintro (rfl | rfl | ⟨x, hx, rfl⟩)
      · right; exact ⟨s, Or.inl rfl, rfl⟩
      · left; rfl
      · right; exact ⟨x, Or.inr hx, rfl⟩
    · rintro (rfl | ⟨x, rfl | hx, rfl⟩)
      · right; left; rfl
      · left; rfl
      · right; right; exact ⟨x, hx, rfl⟩
  have hstep1 : up d s pred A0 A1 := ⟨by omega, none, hnone0, rfl, Or.inl rfl⟩
  have hstep2 : up d s pred A1 A2 :=
    ⟨by omega, some s, hs1, rfl, Or.inr ⟨s, rfl, Or.inl ⟨rfl, Finset.mem_insert_self none A0⟩⟩⟩
  have hstep3 : up d s pred B0 A2 := ⟨by omega, none, hnoneB, hA2eq, Or.inl rfl⟩
  exact Relation.ReflTransGen.tail
    (Relation.ReflTransGen.tail (Relation.ReflTransGen.single (Or.inl hstep1)) (Or.inl hstep2))
    (Or.inr hstep3)

def StaticRep {n : ℕ} (axioms : Finset (Clause (Fin n))) (budget : ℕ) (target : Poly n) : Prop :=
  ∃ (q : Clause (Fin n) → Poly n) (b : Fin n → Poly n),
    (∀ C ∈ axioms, q C = 0 ∨ (q C).totalDegree + (clausePoly C).totalDegree ≤ budget) ∧
    (∀ v, b v = 0 ∨ (b v).totalDegree + 2 ≤ budget) ∧
    axioms.sum (fun C => q C * clausePoly C) + (∑ v, b v * (X v * X v + X v)) = target

theorem staticRep_zero {n : ℕ} (axioms : Finset (Clause (Fin n))) (budget : ℕ) :
    StaticRep axioms budget 0 :=
  ⟨fun _ => 0, fun _ => 0, fun _ _ => Or.inl rfl, fun _ => Or.inl rfl, by simp⟩

theorem staticRep_add {n : ℕ} {axioms : Finset (Clause (Fin n))} {budget : ℕ} {p1 p2 : Poly n}
    (h1 : StaticRep axioms budget p1) (h2 : StaticRep axioms budget p2) :
    StaticRep axioms budget (p1 + p2) := by
  obtain ⟨q1, b1, hq1, hb1, heq1⟩ := h1
  obtain ⟨q2, b2, hq2, hb2, heq2⟩ := h2
  refine ⟨fun C => q1 C + q2 C, fun v => b1 v + b2 v, ?_, ?_, ?_⟩
  · intro C hC
    dsimp only
    rcases hq1 C hC with h10 | h1d <;> rcases hq2 C hC with h20 | h2d
    · left; rw [h10, h20, add_zero]
    · right; rw [h10, zero_add]; exact h2d
    · right; rw [h20, add_zero]; exact h1d
    · right
      have := totalDegree_add (q1 C) (q2 C)
      omega
  · intro v
    dsimp only
    rcases hb1 v with h10 | h1d <;> rcases hb2 v with h20 | h2d
    · left; rw [h10, h20, add_zero]
    · right; rw [h10, zero_add]; exact h2d
    · right; rw [h20, add_zero]; exact h1d
    · right
      have := totalDegree_add (b1 v) (b2 v)
      omega
  · rw [← heq1, ← heq2]
    have hsum1 : axioms.sum (fun C => (q1 C + q2 C) * clausePoly C) =
        axioms.sum (fun C => q1 C * clausePoly C) + axioms.sum (fun C => q2 C * clausePoly C) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun C _ => add_mul _ _ _
    have hsum2 : (∑ v : Fin n, (b1 v + b2 v) * (X v * X v + X v)) =
        (∑ v : Fin n, b1 v * (X v * X v + X v)) + (∑ v : Fin n, b2 v * (X v * X v + X v)) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun v _ => add_mul _ _ _
    rw [hsum1, hsum2]
    ring

theorem staticRep_single {n : ℕ} {axioms : Finset (Clause (Fin n))} {budget : ℕ}
    {C : Clause (Fin n)} (hC : C ∈ axioms) (r : Poly n)
    (hdeg : r.totalDegree + (clausePoly C).totalDegree ≤ budget) :
    StaticRep axioms budget (r * clausePoly C) := by
  classical
  refine ⟨fun C' => if C' = C then r else 0, fun _ => 0, ?_, fun _ => Or.inl rfl, ?_⟩
  · intro C' _
    by_cases h : C' = C
    · subst h; right; simpa using hdeg
    · left; simp [h]
  · simp only [zero_mul, Finset.sum_const_zero, add_zero]
    rw [Finset.sum_eq_single C]
    · simp
    · intro C' _ hne; simp [hne]
    · intro h; exact absurd hC h

def proj {n : ℕ} (U : Finset (Option (Fin n))) : Finset (Fin n) :=
  Finset.univ.filter (fun i : Fin n => some i ∈ U)

theorem proj_empty {n : ℕ} : proj (∅ : Finset (Option (Fin n))) = ∅ := by
  ext i; simp [proj]

theorem proj_image_some {n : ℕ} (S : Finset (Fin n)) : proj (S.image some) = S := by
  ext i
  simp [proj]

theorem card_proj_le {n : ℕ} (U : Finset (Option (Fin n))) : (proj U).card ≤ U.card := by
  have hsub : (proj U).image some ⊆ U := by
    intro z hz
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
    exact (Finset.mem_filter.mp hi).2
  calc (proj U).card = ((proj U).image some).card :=
        (Finset.card_image_of_injective _ (Option.some_injective (Fin n))).symm
    _ ≤ U.card := Finset.card_le_card hsub

theorem card_proj_add_one_le_of_none {n : ℕ} (U : Finset (Option (Fin n))) (hnone : none ∈ U) :
    (proj U).card + 1 ≤ U.card := by
  have hsub : insert none ((proj U).image some) ⊆ U := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact hnone
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
      exact (Finset.mem_filter.mp hi).2
  have hni : none ∉ (proj U).image some := by simp
  calc (proj U).card + 1 = ((proj U).image some).card + 1 := by
        rw [Finset.card_image_of_injective _ (Option.some_injective (Fin n))]
    _ = (insert none ((proj U).image some)).card := (Finset.card_insert_of_notMem hni).symm
    _ ≤ U.card := Finset.card_le_card hsub

theorem dir_forward {n d : ℕ} {s t : Fin n} (hst : s ≠ t)
    (pred : Fin n → Finset (Fin n)) (hpred : ∀ v, v ≠ s → v ∉ pred v)
    (hstat : StaticRep ((Finset.univ.erase s).image (clauseOf pred) ∪ {pin1 s t, pin2 s t, pin3 s t}) d 1) :
    ∃ S : Finset (Fin n), t ∈ S ∧ (S.card < d ∨ s ∈ S) ∧
      Relation.ReflTransGen (stepRel d s pred) ∅ (S.image some) := by
  classical
  by_contra hno
  let F := (Finset.univ.erase s).image (clauseOf pred) ∪ {pin1 s t, pin2 s t, pin3 s t}
  let Comp : Finset (Fin n) → Prop := fun S =>
    Relation.ReflTransGen (stepRel d s pred) ∅ (S.image some)
  let chi : Poly n → ZMod 2 := fun p =>
    ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => Comp S), (nf p).coeff (indF S)
  have hchi_add : ∀ p1 p2 : Poly n, chi (p1 + p2) = chi p1 + chi p2 := by
    intro p1 p2
    simp only [chi, nf_add, coeff_add', Finset.sum_add_distrib]
  have hchi_zero : chi 0 = 0 := by
    simp [chi, nf_zero]
  have hchi_sum : ∀ {ι : Type} (I : Finset ι) (f : ι → Poly n),
      chi (∑ a ∈ I, f a) = ∑ a ∈ I, chi (f a) := by
    intro ι I f
    induction I using Finset.induction_on with
    | empty => simp [hchi_zero]
    | @insert a I ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hchi_add, ih]
  have hchi_mon : ∀ S : Finset (Fin n), chi (mon S) = if Comp S then 1 else 0 := by
    intro S
    have hnf_mon : nf (mon S) = mon S := by
      rw [mon_eq_monomial, nf_monomial, indF_support]
    simp only [chi, hnf_mon, coeff_mon]
    by_cases hS : Comp S
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hS)]
      have hmem : S ∈ Finset.univ.filter (fun T : Finset (Fin n) => Comp T) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ S, hS⟩
      rw [Finset.sum_eq_single S]
      · simp
      · intro T _ hTS; simp [hTS.symm]
      · intro h; exact absurd hmem h
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hS)]
      apply Finset.sum_eq_zero
      intro T hT
      have hTS : S ≠ T := by
        intro e; subst e; exact hS (Finset.mem_filter.mp hT).2
      simp [hTS]
  have hchi_nf : ∀ p : Poly n, chi p = chi (nf p) := by
    intro p
    have hnf2 : nf (nf p) = nf p := by
      conv_lhs => rw [nf_eq_sum_indF p]
      rw [nf_sum]
      conv_rhs => rw [nf_eq_sum_indF p]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [nf_monomial, indF_support]
    simp only [chi, hnf2]
  have hchi_one : chi 1 = 1 := by
    have h1 : (1 : Poly n) = mon ∅ := by simp [mon]
    rw [h1, hchi_mon]
    have hC0 : Comp ∅ := by
      change Relation.ReflTransGen (stepRel d s pred) ∅ ((∅ : Finset (Fin n)).image some)
      simp [Relation.ReflTransGen.refl]
    simp [hC0]
  have hchi_bool : ∀ (p : Poly n) (v : Fin n), chi (p * (X v * X v + X v)) = 0 := by
    intro p v
    rw [hchi_nf, nf_mul_boolAx, hchi_zero]
  have hchi_clause : ∀ v ∈ Finset.univ.erase s, ∀ q : Poly n,
      (q = 0 ∨ q.totalDegree + (clausePoly (clauseOf pred v)).totalDegree ≤ d) →
      chi (q * clausePoly (clauseOf pred v)) = 0 := by
    intro v hv q hq
    rcases hq with rfl | hdeg
    · simp [hchi_zero]
    · have hvs : v ≠ s := (Finset.mem_erase.mp hv).1
      have hv_np : v ∉ pred v := hpred v hvs
      rw [totalDegree_clauseOf pred v hv_np] at hdeg
      rw [q.as_sum, Finset.sum_mul, hchi_sum]
      apply Finset.sum_eq_zero
      intro e he
      have hc : q.coeff e = 1 := zmod2_eq_one_of_ne_zero (mem_support_iff.mp he)
      rw [hc]
      have hed : e.sum (fun _ k => k) ≤ q.totalDegree :=
        Finset.le_sup (f := fun m : Fin n →₀ ℕ => m.sum (fun _ k => k)) he
      have hMcard : e.support.card + (pred v).card + 1 ≤ d := by
        have := card_support_le_sum e
        omega
      rw [hchi_nf, clausePoly_clauseOf pred v hv_np, mul_add, nf_add,
        nf_monomial_mul_mon, nf_monomial_mul_mon, hchi_add, hchi_mon, hchi_mon]
      set A := e.support ∪ pred v
      set B := e.support ∪ insert v (pred v)
      have hBeq : B = insert v A := by
        ext x; simp only [A, B, Finset.mem_union, Finset.mem_insert]; tauto
      by_cases hvA : v ∈ A
      · have hBA : B = A := by rw [hBeq, Finset.insert_eq_of_mem hvA]
        rw [hBA]
        exact zmod2_add_self _
      · have hBcard : B.card ≤ d := by
          rw [hBeq, Finset.card_insert_of_notMem hvA]
          have hA_le : A.card ≤ e.support.card + (pred v).card := Finset.card_union_le _ _
          omega
        have hup : up d s pred (A.image some) (B.image some) := by
          refine ⟨?_, some v, ?_, ?_, ?_⟩
          · rw [Finset.card_image_of_injective _ (Option.some_injective (Fin n))]
            exact hBcard
          · simp [hvA]
          · rw [hBeq, Finset.image_insert]
          · right
            refine ⟨v, rfl, Or.inr ⟨hvs, fun u hu => ?_⟩⟩
            exact Finset.mem_image.mpr ⟨u, Finset.mem_union_right _ hu, rfl⟩
        have hiff : Comp A ↔ Comp B := by
          constructor
          · intro hA; exact Relation.ReflTransGen.tail hA (Or.inl hup)
          · intro hB; exact Relation.ReflTransGen.tail hB (Or.inr hup)
        by_cases hA : Comp A
        · have hB := hiff.mp hA
          simp only [hA, hB, ite_true]
          exact zmod2_add_self 1
        · have hB : ¬ Comp B := fun h => hA (hiff.mpr h)
          simp [hA, hB]
  have hchi_pin_gen : ∀ (e : Fin n →₀ ℕ), e.support.card + 2 ≤ d →
      chi (monomial e (1 : ZMod 2) * (1 + X s)) = 0 ∧
      chi (monomial e (1 : ZMod 2) * X t) = 0 ∧
      chi (monomial e (1 : ZMod 2) * (X t * X s)) = 0 := by
    intro e hec
    refine ⟨?_, ?_, ?_⟩
    · have h1s : (1 + X s : Poly n) = mon ∅ + mon {s} := by simp [mon]
      rw [hchi_nf, h1s, mul_add, nf_add, nf_monomial_mul_mon, nf_monomial_mul_mon,
        hchi_add, hchi_mon, hchi_mon]
      simp only [Finset.union_empty, Finset.union_singleton]
      by_cases hsM : s ∈ e.support
      · rw [Finset.insert_eq_of_mem hsM]
        exact zmod2_add_self _
      · have hbr := bridge_source (d := d) (s := s) (pred := pred) e.support hsM hec
        have hiff : Comp e.support ↔ Comp (insert s e.support) :=
          ⟨fun h => h.trans hbr, fun h => h.trans (rtg_symm hbr)⟩
        by_cases hM : Comp e.support
        · have hM' := hiff.mp hM
          simp only [hM, hM', ite_true]
          exact zmod2_add_self 1
        · have hM' : ¬ Comp (insert s e.support) := fun h => hM (hiff.mpr h)
          simp [hM, hM']
    · have hXt : (X t : Poly n) = mon {t} := by simp [mon]
      rw [hchi_nf, hXt, nf_monomial_mul_mon, Finset.union_singleton, hchi_mon]
      have hnc : ¬ Comp (insert t e.support) := by
        intro hc
        apply hno
        refine ⟨insert t e.support, Finset.mem_insert_self t _, Or.inl ?_, hc⟩
        have := Finset.card_insert_le t e.support
        omega
      simp [hnc]
    · have hXts : (X t * X s : Poly n) = mon {t, s} := by simp [mon, Finset.prod_pair hst.symm]
      rw [hchi_nf, hXts, nf_monomial_mul_mon, hchi_mon]
      have hnc : ¬ Comp (e.support ∪ {t, s}) := by
        intro hc
        apply hno
        refine ⟨e.support ∪ {t, s}, Finset.mem_union_right _ (Finset.mem_insert_self t {s}),
          Or.inr (Finset.mem_union_right _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self s))), hc⟩
      rw [ite_eq_right_of_eq_false _ _ (eq_false hnc)]
  obtain ⟨q, b, hq, hb, heq⟩ := hstat
  have hchi_lhs : chi (F.sum (fun C => q C * clausePoly C) + ∑ v, b v * (X v * X v + X v)) = 0 := by
    rw [hchi_add, hchi_sum, hchi_sum]
    have hb0 : ∑ v : Fin n, chi (b v * (X v * X v + X v)) = 0 :=
      Finset.sum_eq_zero fun v _ => hchi_bool (b v) v
    have hF0 : ∑ C ∈ F, chi (q C * clausePoly C) = 0 := by
      apply Finset.sum_eq_zero
      intro C hCF
      rcases Finset.mem_union.mp hCF with hC1 | hC2
      · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hC1
        exact hchi_clause v hv (q (clauseOf pred v)) (hq _ hCF)
      · have hqC := hq C hCF
        rcases hqC with hq0 | hqdeg
        · rw [hq0, zero_mul, hchi_zero]
        · have hdeg2 : (q C).totalDegree + 2 ≤ d := by
            simp only [Finset.mem_insert, Finset.mem_singleton] at hC2
            rcases hC2 with rfl | rfl | rfl
            · rw [totalDegree_pin1 hst] at hqdeg; exact hqdeg
            · rw [totalDegree_pin2 hst] at hqdeg; exact hqdeg
            · rw [totalDegree_pin3 hst] at hqdeg; exact hqdeg
          rw [(q C).as_sum, Finset.sum_mul, hchi_sum]
          apply Finset.sum_eq_zero
          intro e he
          have hc : (q C).coeff e = 1 := zmod2_eq_one_of_ne_zero (mem_support_iff.mp he)
          rw [hc]
          have hed : e.sum (fun _ k => k) ≤ (q C).totalDegree :=
            Finset.le_sup (f := fun m : Fin n →₀ ℕ => m.sum (fun _ k => k)) he
          have hMcard : e.support.card + 2 ≤ d := by
            have := card_support_le_sum e
            omega
          obtain ⟨hp1, hp2, hp3⟩ := hchi_pin_gen e hMcard
          simp only [Finset.mem_insert, Finset.mem_singleton] at hC2
          rcases hC2 with rfl | rfl | rfl
          · rw [clausePoly_pin1 hst, mul_add, mul_add, hchi_add, hchi_add, hp1, hp2, hp3]
            simp
          · rw [clausePoly_pin2, mul_add, hchi_add, hp2, hp3]
            simp
          · rw [clausePoly_pin3 hst, hp3]
    rw [hF0, hb0, add_zero]
  rw [heq, hchi_one] at hchi_lhs
  exact one_ne_zero hchi_lhs

theorem dir_backward {n d : ℕ} {s t : Fin n} (hst : s ≠ t)
    (pred : Fin n → Finset (Fin n)) (hpred : ∀ v, v ≠ s → v ∉ pred v)
    (S : Finset (Fin n)) (htS : t ∈ S) (hcond : S.card < d ∨ s ∈ S)
    (hpath : Relation.ReflTransGen (stepRel d s pred) ∅ (S.image some)) :
    StaticRep ((Finset.univ.erase s).image (clauseOf pred) ∪ {pin1 s t, pin2 s t, pin3 s t}) d 1 := by
  let F := (Finset.univ.erase s).image (clauseOf pred) ∪ {pin1 s t, pin2 s t, pin3 s t}
  have hpin1 : pin1 s t ∈ F := Finset.mem_union_right _ (by simp)
  have hpin2 : pin2 s t ∈ F := Finset.mem_union_right _ (by simp)
  have hpin3 : pin3 s t ∈ F := Finset.mem_union_right _ (by simp)
  have hup_rep : ∀ A B : Finset (Option (Fin n)), up d s pred A B →
      StaticRep F d (mon (proj A) + mon (proj B)) := by
    intro A B ⟨hBcard, z, hzA, hBeq, hen⟩
    subst hBeq
    rcases hen with rfl | ⟨i, rfl, ⟨his_eq, hnone⟩ | ⟨his, hpi⟩⟩
    · have hpeq : proj (insert none A) = proj A := by
        ext x; simp [proj]
      rw [hpeq, add_self_eq_zero]
      exact staticRep_zero F d
    · rw [his_eq] at hzA hBcard ⊢
      have hns : s ∉ proj A := fun h => hzA (Finset.mem_filter.mp h).2
      have hpeq : proj (insert (some s) A) = insert s (proj A) := by
        ext x
        simp only [proj, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Option.some.injEq]
      have hAcard : (proj A).card + 2 ≤ d := by
        have h1 := card_proj_add_one_le_of_none A hnone
        rw [Finset.card_insert_of_notMem hzA] at hBcard
        omega
      have hsum : mon (proj A) + mon (proj (insert (some s) A)) =
          mon (proj A) * clausePoly (pin1 s t) + mon (proj A) * clausePoly (pin2 s t) := by
        rw [hpeq, clausePoly_pin1 hst, clausePoly_pin2]
        have h1 : mon (insert s (proj A)) = X s * mon (proj A) := by
          unfold mon; rw [Finset.prod_insert hns]
        rw [h1]
        have h2 : mon (proj A) * (1 + X s + X t + X t * X s) + mon (proj A) * (X t + X t * X s) =
            mon (proj A) + X s * mon (proj A) +
            (mon (proj A) * (X t + X t * X s) + mon (proj A) * (X t + X t * X s)) := by ring
        rw [h2, add_self_eq_zero, add_zero]
      rw [hsum]
      refine staticRep_add ?_ ?_
      · exact staticRep_single hpin1 (mon (proj A))
          (by rw [totalDegree_pin1 hst]; exact (Nat.add_le_add_right (totalDegree_mon_le _) 2).trans hAcard)
      · exact staticRep_single hpin2 (mon (proj A))
          (by rw [totalDegree_pin2 hst]; exact (Nat.add_le_add_right (totalDegree_mon_le _) 2).trans hAcard)
    · have hni : i ∉ proj A := fun h => hzA (Finset.mem_filter.mp h).2
      have hpeq : proj (insert (some i) A) = insert i (proj A) := by
        ext x
        simp only [proj, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Option.some.injEq]
      have hsub : pred i ⊆ proj A := fun u hu => Finset.mem_filter.mpr ⟨Finset.mem_univ u, hpi u hu⟩
      let R := proj A \ pred i
      have hdisj1 : Disjoint R (pred i) := disjoint_sdiff_self_left
      have hU1 : R ∪ pred i = proj A := Finset.sdiff_union_of_subset hsub
      have hni_R : i ∉ R := fun h => hni (Finset.mem_sdiff.mp h).1
      have hdisj2 : Disjoint R (insert i (pred i)) := Finset.disjoint_insert_right.mpr ⟨hni_R, hdisj1⟩
      have hU2 : R ∪ insert i (pred i) = insert i (proj A) := by
        ext x
        simp only [Finset.mem_union, Finset.mem_insert]
        constructor
        · rintro (hR | rfl | hp)
          · right; exact (Finset.mem_sdiff.mp hR).1
          · left; rfl
          · right; exact hsub hp
        · rintro (rfl | hA)
          · right; left; rfl
          · by_cases hp : x ∈ pred i
            · right; right; exact hp
            · left; exact Finset.mem_sdiff.mpr ⟨hA, hp⟩
      have hRcard : R.card + ((pred i).card + 1) ≤ d := by
        have h1 : R.card + (pred i).card = (proj A).card := by
          rw [← Finset.card_union_of_disjoint hdisj1, hU1]
        have h2 : (proj A).card + 1 = (proj (insert (some i) A)).card := by
          rw [hpeq, Finset.card_insert_of_notMem hni]
        have h3 := card_proj_le (insert (some i) A)
        omega
      have hcl : clauseOf pred i ∈ F :=
        Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, Finset.mem_erase.mpr ⟨his, Finset.mem_univ i⟩, rfl⟩)
      have heq : mon (proj A) + mon (proj (insert (some i) A)) =
          mon R * clausePoly (clauseOf pred i) := by
        rw [hpeq, clausePoly_clauseOf pred i (hpred i his), mul_add,
          mon_mul_disjoint hdisj1, hU1, mon_mul_disjoint hdisj2, hU2]
      rw [heq]
      refine staticRep_single hcl (mon R) ?_
      rw [totalDegree_clauseOf pred i (hpred i his)]
      exact (Nat.add_le_add_right (totalDegree_mon_le R) _).trans hRcard
  have hpath_rep : ∀ U V : Finset (Option (Fin n)),
      Relation.ReflTransGen (stepRel d s pred) U V →
      StaticRep F d (mon (proj U) + mon (proj V)) := by
    intro U V h
    induction h with
    | refl =>
      rw [add_self_eq_zero]
      exact staticRep_zero F d
    | @tail b c _ hstep ih =>
      have hsrep : StaticRep F d (mon (proj b) + mon (proj c)) := by
        rcases hstep with h1 | h2
        · exact hup_rep b c h1
        · rw [add_comm]
          exact hup_rep c b h2
      have hsum := staticRep_add ih hsrep
      have hcancel : (mon (proj U) + mon (proj b)) + (mon (proj b) + mon (proj c)) =
          mon (proj U) + mon (proj c) := by
        calc (mon (proj U) + mon (proj b)) + (mon (proj b) + mon (proj c))
            = mon (proj U) + (mon (proj b) + mon (proj b)) + mon (proj c) := by ring
          _ = mon (proj U) + 0 + mon (proj c) := by rw [add_self_eq_zero]
          _ = mon (proj U) + mon (proj c) := by ring
      rwa [hcancel] at hsum
  have h1S : StaticRep F d (1 + mon S) := by
    have h := hpath_rep ∅ (S.image some) hpath
    rw [proj_empty, proj_image_some] at h
    simpa [mon] using h
  have hScard : S.card ≤ d := by
    have hne : (S.image some) ≠ ∅ := by
      intro h
      have : some t ∈ (∅ : Finset (Option (Fin n))) := h ▸ Finset.mem_image.mpr ⟨t, htS, rfl⟩
      exact Finset.notMem_empty _ this
    have hcard_gen : ∀ W : Finset (Option (Fin n)),
        Relation.ReflTransGen (stepRel d s pred) ∅ W → W ≠ ∅ → W.card ≤ d := by
      intro W hW hWne
      cases hW with
      | refl => exact absurd rfl hWne
      | tail _ hstep =>
        rcases hstep with ⟨hB, _⟩ | ⟨hB, z, _, hBeq, _⟩
        · exact hB
        · have hle : W.card ≤ (insert z W).card := Finset.card_le_card (Finset.subset_insert _ _)
          rw [← hBeq] at hle
          omega
    have := hcard_gen (S.image some) hpath hne
    rwa [Finset.card_image_of_injective _ (Option.some_injective (Fin n))] at this
  have hS : StaticRep F d (mon S) := by
    rcases hcond with hlt | hsS
    · set R := S.erase t
      have hRcard : R.card + 2 ≤ d := by
        have hR : R.card = S.card - 1 := Finset.card_erase_of_mem htS
        have hpos : 1 ≤ S.card := Finset.card_pos.mpr ⟨t, htS⟩
        omega
      have heq : mon S = mon R * clausePoly (pin2 s t) + mon R * clausePoly (pin3 s t) := by
        rw [clausePoly_pin2, clausePoly_pin3 hst]
        have h1 : mon S = X t * mon R := by
          unfold mon R
          conv_lhs => rw [← Finset.insert_erase htS]
          rw [Finset.prod_insert (Finset.notMem_erase t S)]
        rw [h1]
        have h2 : mon R * (X t + X t * X s) + mon R * (X t * X s) =
            X t * mon R + (mon R * (X t * X s) + mon R * (X t * X s)) := by ring
        rw [h2, add_self_eq_zero, add_zero]
      rw [heq]
      refine staticRep_add ?_ ?_
      · exact staticRep_single hpin2 (mon R)
          (by rw [totalDegree_pin2 hst]; exact (Nat.add_le_add_right (totalDegree_mon_le R) 2).trans hRcard)
      · exact staticRep_single hpin3 (mon R)
          (by rw [totalDegree_pin3 hst]; exact (Nat.add_le_add_right (totalDegree_mon_le R) 2).trans hRcard)
    · set R := (S.erase t).erase s
      have hs_er : s ∈ S.erase t := Finset.mem_erase.mpr ⟨hst, hsS⟩
      have hRcard : R.card + 2 ≤ d := by
        have h1 : R.card = (S.erase t).card - 1 := Finset.card_erase_of_mem hs_er
        have h2 : (S.erase t).card = S.card - 1 := Finset.card_erase_of_mem htS
        have h3 : 2 ≤ S.card := by
          have : ({s, t} : Finset (Fin n)) ⊆ S := by
            intro x hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl
            · exact hsS
            · exact htS
          have h4 := Finset.card_le_card this
          rw [Finset.card_pair hst] at h4
          exact h4
        omega
      have heq : mon S = mon R * clausePoly (pin3 s t) := by
        rw [clausePoly_pin3 hst]
        have h1 : mon S = X t * (X s * mon R) := by
          unfold mon R
          conv_lhs => rw [← Finset.insert_erase htS]
          rw [Finset.prod_insert (Finset.notMem_erase t S)]
          congr 1
          conv_lhs => rw [← Finset.insert_erase hs_er]
          rw [Finset.prod_insert (Finset.notMem_erase s (S.erase t))]
        rw [h1]
        ring
      rw [heq]
      exact staticRep_single hpin3 (mon R)
        (by rw [totalDegree_pin3 hst]; exact (Nat.add_le_add_right (totalDegree_mon_le R) 2).trans hRcard)
  have hsum := staticRep_add h1S hS
  have hcancel : (1 + mon S) + mon S = (1 : Poly n) := by
    calc (1 + mon S) + mon S = 1 + (mon S + mon S) := add_assoc _ _ _
      _ = 1 + 0 := by rw [add_self_eq_zero]
      _ = 1 := add_zero 1
  rwa [hcancel] at hsum

theorem main (n d : ℕ) (s t : Fin n) (hst : s ≠ t)
    (pred : Fin n → Finset (Fin n)) (hpred : ∀ v, v ≠ s → v ∉ pred v) :
    StaticRep ((Finset.univ.erase s).image (clauseOf pred) ∪ {pin1 s t, pin2 s t, pin3 s t}) d 1 ↔
      ∃ S : Finset (Fin n), t ∈ S ∧ (S.card < d ∨ s ∈ S) ∧
        Relation.ReflTransGen (stepRel d s pred) ∅ (S.image some) :=
  ⟨dir_forward hst pred hpred, fun ⟨S, htS, hcond, hpath⟩ =>
    dir_backward hst pred hpred S htS hcond hpath⟩

def prd (n : ℕ) (v : Fin n) : Finset (Fin n) := Finset.univ.filter (fun u => u.val + 1 = v.val)

theorem mem_prd {n : ℕ} (u v : Fin n) : u ∈ prd n v ↔ u.val + 1 = v.val := by
  simp [prd]

def s0 (n : ℕ) (hn : 0 < n) : Fin n := ⟨0, hn⟩

def t0 (n : ℕ) (hn : 0 < n) : Fin n := ⟨n - 1, Nat.sub_lt hn Nat.one_pos⟩

def blk (n : ℕ) : Finset (Fin n × (Bool × Bool)) :=
  (Finset.univ : Finset (Fin n × (Bool × Bool))).filter
    (fun z => (if z.1.val+1 = n then (!z.2.1 && z.2.2) else (!z.2.1 || z.2.2)) = false)

def rowC (n : ℕ) (hn : 0 < n) (row : Fin n × (Bool × Bool)) : Clause (Fin n) :=
  {(row.1, !row.2.1), ((⟨(row.1.val+1) % n, Nat.mod_lt _ hn⟩ : Fin n), !row.2.2)}

theorem row_mid {n : ℕ} (hn : 0 < n) (v : Fin n) (hv : v.val ≠ 0) :
    clauseOf (prd n) v = rowC n hn (⟨v.val - 1, by have := v.isLt; omega⟩, true, false) := by
  have hp : prd n v = {(⟨v.val - 1, by have := v.isLt; omega⟩ : Fin n)} := by
    ext u
    rw [mem_prd, Finset.mem_singleton, Fin.ext_iff]
    show u.val + 1 = v.val ↔ u.val = v.val - 1
    omega
  have hpos : (⟨(v.val - 1 + 1) % n, Nat.mod_lt _ hn⟩ : Fin n) = v := by
    apply Fin.ext
    show (v.val - 1 + 1) % n = v.val
    have h1 : v.val - 1 + 1 = v.val := by omega
    rw [h1, Nat.mod_eq_of_lt v.isLt]
  unfold clauseOf rowC
  rw [hp, Finset.image_singleton]
  show insert (v, true) {((⟨v.val - 1, _⟩ : Fin n), false)} =
    {((⟨v.val - 1, _⟩ : Fin n), !true), ((⟨(v.val - 1 + 1) % n, Nat.mod_lt _ hn⟩ : Fin n), !false)}
  rw [hpos]
  exact Finset.pair_comm _ _

theorem row_last {n : ℕ} (hn : 0 < n) (a b : Bool) :
    rowC n hn (t0 n hn, a, b) = {(t0 n hn, !a), (s0 n hn, !b)} := by
  have hpos : (⟨((t0 n hn).val + 1) % n, Nat.mod_lt _ hn⟩ : Fin n) = s0 n hn := by
    apply Fin.ext
    show (n - 1 + 1) % n = 0
    have h1 : n - 1 + 1 = n := by omega
    rw [h1, Nat.mod_self]
  unfold rowC
  show {(t0 n hn, !a), ((⟨((t0 n hn).val + 1) % n, Nat.mod_lt _ hn⟩ : Fin n), !b)} = _
  rw [hpos]

theorem t0_val {n : ℕ} (hn : 0 < n) : (t0 n hn).val + 1 = n := by
  show n - 1 + 1 = n
  omega

theorem F_eq (n : ℕ) (hn : 0 < n) :
    (blk n).image (rowC n hn) =
      (Finset.univ.erase (s0 n hn)).image (clauseOf (prd n)) ∪
        {pin1 (s0 n hn) (t0 n hn), pin2 (s0 n hn) (t0 n hn), pin3 (s0 n hn) (t0 n hn)} := by
  ext C
  constructor
  · intro hC
    obtain ⟨⟨i, a, b⟩, hrow, rfl⟩ := Finset.mem_image.mp hC
    have hrow' : (if i.val+1 = n then (!a && b) else (!a || b)) = false :=
      (Finset.mem_filter.mp hrow).2
    by_cases hi : i.val + 1 = n
    · have hit : i = t0 n hn := Fin.ext (by show i.val = n - 1; omega)
      rw [if_pos hi] at hrow'
      apply Finset.mem_union_right
      rw [hit, row_last]
      rcases a with _ | _ <;> rcases b with _ | _
      · exact Finset.mem_insert_self _ _
      · exact absurd hrow' (by decide)
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    · rw [if_neg hi] at hrow'
      have hlt : i.val + 1 < n := by have := i.isLt; omega
      rcases a with _ | _ <;> rcases b with _ | _
      · exact absurd hrow' (by decide)
      · exact absurd hrow' (by decide)
      · apply Finset.mem_union_left
        refine Finset.mem_image.mpr ⟨⟨i.val + 1, hlt⟩, Finset.mem_erase.mpr ⟨fun h => ?_, Finset.mem_univ _⟩, ?_⟩
        · have h1 := congrArg Fin.val h
          have h2 : i.val + 1 = 0 := h1
          omega
        · rw [row_mid hn ⟨i.val + 1, hlt⟩ (by show i.val + 1 ≠ 0; omega)]
          rfl
      · exact absurd hrow' (by decide)
  · intro hC
    rcases Finset.mem_union.mp hC with h | h
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp h
      have hv0 : v.val ≠ 0 := fun h0 => (Finset.mem_erase.mp hv).1 (Fin.ext h0)
      rw [row_mid hn v hv0]
      refine Finset.mem_image.mpr ⟨_, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
      have hne : ¬ (v.val - 1 + 1 = n) := by have := v.isLt; omega
      show (if v.val - 1 + 1 = n then (!true && false) else (!true || false)) = false
      rw [if_neg hne]
      rfl
    · simp only [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with rfl | rfl | rfl
      · refine Finset.mem_image.mpr ⟨(t0 n hn, false, false), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, row_last hn false false⟩
        show (if (t0 n hn).val + 1 = n then (!false && false) else (!false || false)) = false
        rw [if_pos (t0_val hn)]
        rfl
      · refine Finset.mem_image.mpr ⟨(t0 n hn, true, false), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, row_last hn true false⟩
        show (if (t0 n hn).val + 1 = n then (!true && false) else (!true || false)) = false
        rw [if_pos (t0_val hn)]
        rfl
      · refine Finset.mem_image.mpr ⟨(t0 n hn, true, true), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, row_last hn true true⟩
        show (if (t0 n hn).val + 1 = n then (!true && true) else (!true || true)) = false
        rw [if_pos (t0_val hn)]
        rfl

def encP {n : ℕ} (z : Option (Fin n)) : ℕ := z.elim 1 (fun i => i.val + 2)

theorem encP_none {n : ℕ} : encP (none : Option (Fin n)) = 1 := rfl

theorem encP_some {n : ℕ} (i : Fin n) : encP (some i) = i.val + 2 := rfl

theorem encP_inj {n : ℕ} : Function.Injective (encP : Option (Fin n) → ℕ) := by
  intro a b h
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some j => rw [encP_none, encP_some] at h; omega
  | some i =>
    cases b with
    | none => rw [encP_none, encP_some] at h; omega
    | some j =>
      rw [encP_some, encP_some] at h
      exact congrArg some (Fin.ext (by omega))

theorem hen_of_enabled {n : ℕ} (hn : 0 < n) {z : Option (Fin n)} {A : Finset (Option (Fin n))}
    (h : enabled (s0 n hn) (prd n) z A) :
    encP z = 1 ∨ ∃ x ∈ A.image encP, encP z = x + 1 := by
  rcases h with rfl | ⟨i, rfl, h | h⟩
  · exact Or.inl rfl
  · right
    refine ⟨1, Finset.mem_image.mpr ⟨none, h.2, rfl⟩, ?_⟩
    rw [encP_some, h.1]
    rfl
  · right
    have hi0 : i.val ≠ 0 := fun h0 => h.1 (Fin.ext h0)
    have hlt : i.val - 1 < n := by have := i.isLt; omega
    have hu : (⟨i.val - 1, hlt⟩ : Fin n) ∈ prd n i :=
      (mem_prd _ _).mpr (by show i.val - 1 + 1 = i.val; omega)
    refine ⟨encP (some (⟨i.val - 1, hlt⟩ : Fin n)), Finset.mem_image_of_mem _ (h.2 _ hu), ?_⟩
    rw [encP_some, encP_some]
    show i.val + 2 = i.val - 1 + 2 + 1
    omega

theorem lower_up {n d : ℕ} (hn : 0 < n) {A B : Finset (Option (Fin n))}
    (h : up d (s0 n hn) (prd n) A B) :
    Good d (A.image encP) ↔ Good d (B.image encP) := by
  obtain ⟨hcard, z, hz, rfl, hen⟩ := h
  have hnot : encP z ∉ A.image encP := fun hm => by
    obtain ⟨w, hw, hwz⟩ := Finset.mem_image.mp hm
    have hwz' : w = z := encP_inj hwz
    exact hz (hwz' ▸ hw)
  have hc : (A.image encP).card < d := by
    rw [Finset.card_image_of_injective _ encP_inj]
    rw [Finset.card_insert_of_notMem hz] at hcard
    omega
  rw [Finset.image_insert]
  exact ⟨fun g => good_insert g hnot (hen_of_enabled hn hen) hc,
    fun g => good_erase g hnot (hen_of_enabled hn hen)⟩

theorem lower {n d : ℕ} (hn : 0 < n) {A : Finset (Option (Fin n))}
    (h : Relation.ReflTransGen (stepRel d (s0 n hn) (prd n)) ∅ A) : Good d (A.image encP) := by
  induction h with
  | refl => rw [Finset.image_empty]; exact good_empty d
  | tail _ hstep ih =>
    rcases hstep with hu | hu
    · exact (lower_up hn hu).mp ih
    · exact (lower_up hn hu).mpr ih

def decP (n : ℕ) (p : ℕ) : Option (Fin n) :=
  if h : 2 ≤ p ∧ p < n + 2 then some ⟨p - 2, by omega⟩ else none

theorem encP_decP {n p : ℕ} (h1 : 1 ≤ p) (h2 : p ≤ n + 1) : encP (decP n p) = p := by
  unfold decP
  split
  · rw [encP_some]
    show p - 2 + 2 = p
    omega
  · rw [encP_none]
    omega

theorem enabled_of_hen {n : ℕ} (hn : 0 < n) {A : Finset (Option (Fin n))} {p : ℕ}
    (h1 : 1 ≤ p) (h2 : p ≤ n + 1)
    (hen : p = 1 ∨ ∃ x ∈ A.image encP, p = x + 1) :
    enabled (s0 n hn) (prd n) (decP n p) A := by
  by_cases hp1 : p = 1
  · left
    unfold decP
    rw [dif_neg (by omega)]
  · right
    have hp2 : 2 ≤ p ∧ p < n + 2 := by omega
    obtain ⟨x, hx, hpx⟩ := hen.resolve_left hp1
    obtain ⟨w, hw, hwx⟩ := Finset.mem_image.mp hx
    refine ⟨⟨p - 2, by omega⟩, by unfold decP; rw [dif_pos hp2], ?_⟩
    by_cases hp : p = 2
    · left
      refine ⟨Fin.ext (by show p - 2 = 0; omega), ?_⟩
      cases w with
      | none => exact hw
      | some j => rw [encP_some] at hwx; omega
    · right
      refine ⟨fun h => hp ?_, fun u hu => ?_⟩
      · have h3 := congrArg Fin.val h
        have h4 : p - 2 = 0 := h3
        omega
      · rw [mem_prd] at hu
        have hu' : u.val + 1 = p - 2 := hu
        cases w with
        | none => rw [encP_none] at hwx; omega
        | some j =>
          rw [encP_some] at hwx
          have hju : j = u := Fin.ext (by omega)
          rw [← hju]
          exact hw

theorem upper {n d : ℕ} (hn : 0 < n) {T : Finset ℕ} (h : Rch d (n + 1) ∅ T) :
    ∃ A : Finset (Option (Fin n)), A.image encP = T ∧
      Relation.ReflTransGen (stepRel d (s0 n hn) (prd n)) ∅ A := by
  induction h with
  | refl => exact ⟨∅, Finset.image_empty _, Relation.ReflTransGen.refl⟩
  | @tail T1 T2 _ hstep ih =>
    obtain ⟨A, hA, hpath⟩ := ih
    rcases hstep with ⟨hcard, p, hp, hB, h1, h2, hen⟩ | ⟨hcard, p, hp, hB, h1, h2, hen⟩
    · have hz : decP n p ∉ A := fun hm => hp (by
        rw [← hA, ← encP_decP h1 h2]
        exact Finset.mem_image_of_mem _ hm)
      have himg : (insert (decP n p) A).image encP = insert p (A.image encP) := by
        rw [Finset.image_insert, encP_decP h1 h2]
      refine ⟨insert (decP n p) A, by rw [himg, hA, hB],
        hpath.tail (Or.inl ⟨?_, decP n p, hz, rfl, enabled_of_hen hn h1 h2 (by rw [hA]; exact hen)⟩)⟩
      rw [← Finset.card_image_of_injective _ encP_inj, himg, hA, ← hB]
      exact hcard
    · have hzA : decP n p ∈ A := by
        have hpm : p ∈ A.image encP := by rw [hA, hB]; exact Finset.mem_insert_self _ _
        obtain ⟨w, hw, hwp⟩ := Finset.mem_image.mp hpm
        have hwz : w = decP n p := encP_inj (by rw [hwp, encP_decP h1 h2])
        rw [← hwz]
        exact hw
      have himg : (A.erase (decP n p)).image encP = T2 := by
        rw [Finset.image_erase encP_inj, hA, hB, encP_decP h1 h2, Finset.erase_insert hp]
      refine ⟨A.erase (decP n p), himg,
        hpath.tail (Or.inr ⟨?_, decP n p, Finset.notMem_erase _ _, (Finset.insert_erase hzA).symm,
          enabled_of_hen hn h1 h2 (by rw [himg]; exact hen)⟩)⟩
      rw [← Finset.card_image_of_injective _ encP_inj, hA]
      exact hcard

theorem finish {n d : ℕ} (hn : 0 < n) {A : Finset (Option (Fin n))}
    (hnone : (1 : ℕ) ∉ A.image encP)
    (hpath : Relation.ReflTransGen (stepRel d (s0 n hn) (prd n)) ∅ A)
    (ht : n + 1 ∈ A.image encP)
    (hc : (A.image encP).card < d ∨ 2 ∈ A.image encP) :
    ∃ S : Finset (Fin n), t0 n hn ∈ S ∧ (S.card < d ∨ s0 n hn ∈ S) ∧
      Relation.ReflTransGen (stepRel d (s0 n hn) (prd n)) ∅ (S.image some) := by
  have hnA : none ∉ A := fun hm => hnone (Finset.mem_image.mpr ⟨none, hm, rfl⟩)
  have hAS : (Finset.eraseNone A).image some = A := by
    rw [Finset.image_some_eraseNone, Finset.erase_eq_of_notMem hnA]
  have key : ∀ i : Fin n, i.val + 2 ∈ A.image encP → i ∈ Finset.eraseNone A := fun i hi => by
    obtain ⟨w, hw, hwe⟩ := Finset.mem_image.mp hi
    have hwi : w = some i := encP_inj (by rw [hwe, encP_some])
    rw [Finset.mem_eraseNone, ← hwi]
    exact hw
  have ht' : (t0 n hn).val + 2 ∈ A.image encP := by
    have h1 : (t0 n hn).val + 2 = n + 1 := by have := t0_val hn; omega
    rw [h1]
    exact ht
  refine ⟨Finset.eraseNone A, key _ ht', ?_, by rw [hAS]; exact hpath⟩
  rcases hc with hc | h2
  · left
    rw [← Finset.card_image_of_injective _ (Option.some_injective _), hAS,
      ← Finset.card_image_of_injective _ encP_inj]
    exact hc
  · right
    exact key (s0 n hn) h2

theorem final (n : ℕ) (hn : 0 < n) (hn2 : 2 ≤ n) (d : ℕ) :
    StaticRep ((blk n).image (rowC n hn)) d 1 ↔ (n = 2 ∧ 2 ≤ d) ∨ n + 2 < 2 ^ d := by
  have hst : s0 n hn ≠ t0 n hn := fun h => by
    have h1 := congrArg Fin.val h
    have h2 : 0 = n - 1 := h1
    omega
  have hpred : ∀ v : Fin n, v ≠ s0 n hn → v ∉ prd n v := fun v _ hv => by
    rw [mem_prd] at hv
    omega
  rw [F_eq n hn, main n d (s0 n hn) (t0 n hn) hst (prd n) hpred]
  constructor
  · rintro ⟨S, htS, hcond, hpath⟩
    have hg := lower hn hpath
    have hmem : n + 1 ∈ (S.image some).image encP := by
      have h1 : encP (some (t0 n hn)) = n + 1 := by
        rw [encP_some]
        have := t0_val hn
        omega
      rw [← h1]
      exact Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ htS)
    have hb := good_bound hg hmem
    by_cases hlt : n + 2 < 2 ^ d
    · exact Or.inr hlt
    · have heq : n + 1 + 1 = 2 ^ d := by omega
      rcases hcond with hc | hs
      · exfalso
        have hnot : n + 1 + 1 ∉ (S.image some).image encP := fun hm => by
          obtain ⟨w, hw, hwe⟩ := Finset.mem_image.mp hm
          obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hw
          rw [encP_some] at hwe
          have := i.isLt
          omega
        have hcard : ((S.image some).image encP).card < d := by
          rw [Finset.card_image_of_injective _ encP_inj,
            Finset.card_image_of_injective _ (Option.some_injective _)]
          exact hc
        have hg2 := good_insert hg hnot (Or.inr ⟨n + 1, hmem, rfl⟩) hcard
        have hb2 := good_bound hg2 (Finset.mem_insert_self _ _)
        omega
      · left
        have h2 : 2 ∈ (S.image some).image encP :=
          Finset.mem_image.mpr ⟨some (s0 n hn), Finset.mem_image_of_mem _ hs, rfl⟩
        have hd := good_top hg hmem heq h2
        subst hd
        have h4 : (2 : ℕ) ^ 2 = 4 := by norm_num
        constructor <;> omega
  · intro h
    apply (fun x : ∃ A : Finset (Option (Fin n)), (1 : ℕ) ∉ A.image encP ∧
        Relation.ReflTransGen (stepRel d (s0 n hn) (prd n)) ∅ A ∧ n + 1 ∈ A.image encP ∧
        ((A.image encP).card < d ∨ 2 ∈ A.image encP) => by
      obtain ⟨A, h1, h2, h3, h4⟩ := x
      exact finish hn h1 h2 h3 h4)
    rcases h with ⟨hn2', hd⟩ | hlt
    · subst hn2'
      obtain ⟨A, hA, hpath⟩ := upper hn (strat_two d hd)
      exact ⟨A, by rw [hA]; decide, hpath, by rw [hA]; decide, Or.inr (by rw [hA]; decide)⟩
    · obtain ⟨S, hS1, hSc, hSr, hrch⟩ := strat d n hn2 hlt
      obtain ⟨A, hA, hpath⟩ := upper hn hrch
      refine ⟨A, ?_, hpath, by rw [hA]; exact hS1, Or.inl (by rw [hA]; exact hSc)⟩
      rw [hA]
      intro h1
      have := (hSr 1 h1).1
      omega

end PEqualNP.Outside.L_pcx_243_aux

theorem PEqualNP.Outside.L_pcx_243 : (∀ (n : ℕ) (hn : 0 < n), 2 ≤ n →
  let P := MvPolynomial (Fin n) (ZMod 2)
  let static := fun (axioms : Finset (PEqualNP.ProofComplexity.Clause (Fin n))) (budget : ℕ) =>
    ∃ (q : PEqualNP.ProofComplexity.Clause (Fin n) → P) (b : Fin n → P),
      (∀ C ∈ axioms, q C = 0 ∨ (q C).totalDegree + (PEqualNP.ProofComplexity.clausePoly C).totalDegree ≤ budget) ∧
      (∀ v, b v = 0 ∨ (b v).totalDegree + 2 ≤ budget) ∧
      axioms.sum (fun C => q C * PEqualNP.ProofComplexity.clausePoly C) +
        (∑ v, b v * (MvPolynomial.X v * MvPolynomial.X v + MvPolynomial.X v)) = 1
  let pos := fun i : ℕ => (⟨i % n, Nat.mod_lt _ hn⟩ : Fin n)
  let allowed := fun (i : Fin n) (a b : Bool) =>
    if i.val+1 = n then (!a && b) else (!a || b)
  let blocks := (Finset.univ : Finset (Fin n × (Bool × Bool))).filter
    (fun z => allowed z.1 z.2.1 z.2.2 = false)
  let F : Finset (PEqualNP.ProofComplexity.Clause (Fin n)) := blocks.image (fun row =>
    {(row.1, !row.2.1), (pos (row.1.val+1), !row.2.2)})
  ∀ d : ℕ, static F d ↔ (n = 2 ∧ 2 ≤ d) ∨ n+2 < 2^d) := by
  intro n hn hn2
  dsimp only
  intro d
  exact PEqualNP.Outside.L_pcx_243_aux.final n hn hn2 d
