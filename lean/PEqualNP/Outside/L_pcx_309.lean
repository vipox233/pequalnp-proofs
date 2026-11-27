import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_309_aux


def bal (r t : Nat) : Nat := (t / r) ^ (r - t % r) * (t / r + 1) ^ (t % r)

lemma bal_zero (t : Nat) : bal 0 t = 1 := by
  simp [bal]

lemma bal_eq {r k j : Nat} (hj : j < r) : bal r (r * k + j) = k ^ (r - j) * (k + 1) ^ j := by
  have hr : 0 < r := by omega
  have h1 : (r * k + j) / r = k := by
    rw [Nat.mul_comm, Nat.add_comm, Nat.add_mul_div_right _ _ hr, Nat.div_eq_of_lt hj, Nat.zero_add]
  have h2 : (r * k + j) % r = j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
  simp [bal, h1, h2]


lemma bal_small {r t : Nat} (ht : t < r) : bal r t = 0 := by
  have := bal_eq (k := 0) ht
  rw [Nat.mul_zero, Nat.zero_add] at this
  rw [this]
  have : r - t ≠ 0 := by omega
  simp [this]

lemma bal_ratio {r : Nat} (hr : 0 < r) (s : Nat) :
    bal r (s + 1) * (s / r) = bal r s * (s / r + 1) := by
  have hs : s = r * (s / r) + s % r := (Nat.div_add_mod s r).symm
  have hj : s % r < r := Nat.mod_lt _ hr
  generalize s / r = k at hs
  generalize s % r = j at hs hj
  subst hs
  rw [bal_eq hj]
  by_cases hj1 : j + 1 < r
  · rw [show r * k + j + 1 = r * k + (j + 1) by ring, bal_eq hj1]
    have : r - j = (r - (j + 1)) + 1 := by omega
    rw [this]; ring
  · have hjr : j + 1 = r := by omega
    rw [show r * k + j + 1 = r * (k + 1) + 0 by rw [← hjr]; ring, bal_eq hr]
    have : r - j = 1 := by omega
    rw [this, ← hjr]; simp only [Nat.sub_zero, pow_zero, mul_one]; ring

lemma bal_K2 {r : Nat} (hr : 0 < r) (T : Nat) : bal (r + 1) (T + T / r) = (T / r) * bal r T := by
  have hs : T = r * (T / r) + T % r := (Nat.div_add_mod T r).symm
  have hj : T % r < r := Nat.mod_lt _ hr
  generalize T / r = k at hs ⊢
  generalize T % r = j at hs hj
  subst hs
  rw [bal_eq hj, show r * k + j + k = (r + 1) * k + j by ring, bal_eq (by omega : j < r + 1)]
  have : r + 1 - j = (r - j) + 1 := by omega
  rw [this]; ring

lemma bal_peel {r : Nat} (hr : 0 < r) (T : Nat) :
    bal (r + 1) T = (T / (r + 1)) * bal r (T - T / (r + 1)) := by
  have hs : T = (r + 1) * (T / (r + 1)) + T % (r + 1) := (Nat.div_add_mod T (r + 1)).symm
  have hj : T % (r + 1) < r + 1 := Nat.mod_lt _ (by omega)
  generalize T / (r + 1) = a at hs ⊢
  generalize T % (r + 1) = j at hs hj
  subst hs
  rw [bal_eq hj]
  by_cases hjr : j < r
  · rw [show (r + 1) * a + j - a = r * a + j by
      have : (r + 1) * a = r * a + a := by ring
      omega, bal_eq hjr]
    have : r + 1 - j = (r - j) + 1 := by omega
    rw [this]; ring
  · have hjr' : j = r := by omega
    subst hjr'
    rw [show (j + 1) * a + j - a = j * (a + 1) + 0 by
      have : (j + 1) * a = j * a + a := by ring
      have : j * (a + 1) = j * a + j := by ring
      omega, bal_eq hr]
    simp

lemma bal_mono_succ {r : Nat} (hr : 0 < r) (s : Nat) : bal r s ≤ bal r (s + 1) := by
  by_cases hc : s / r = 0
  · have : s < r := by
      rcases Nat.lt_or_ge s r with h | h
      · exact h
      · exact absurd (Nat.div_pos h hr) (by omega)
    rw [bal_small this]; exact Nat.zero_le _
  · have h := bal_ratio hr s
    have hcpos : 0 < s / r := Nat.pos_of_ne_zero hc
    apply Nat.le_of_mul_le_mul_right _ hcpos
    rw [h]; exact Nat.mul_le_mul_left _ (Nat.le_succ _)

lemma bal_mono {r : Nat} (hr : 0 < r) {s t : Nat} (h : s ≤ t) : bal r s ≤ bal r t := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact le_trans ih (bal_mono_succ hr _)

lemma bal_K {r : Nat} (hr : 0 < r) (T a : Nat) : a * bal r T ≤ bal (r + 1) (T + a) := by
  set k := T / r with hk
  set b := bal r T with hb
  by_cases hk0 : k = 0
  · have : T < r := by
      rcases Nat.lt_or_ge T r with h | h
      · exact h
      · exact absurd (Nat.div_pos h hr) (by omega)
    rw [hb, bal_small this, Nat.mul_zero]; exact Nat.zero_le _
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
  have hT1 : r * k ≤ T := Nat.mul_div_le T r
  have hT2 : T < r * (k + 1) := by
    have := Nat.lt_mul_div_succ T hr
    rw [hk]; linarith [this]
  have hbase : k * b ≤ bal (r + 1) (T + k) := by rw [hk, hb, bal_K2 hr T]
  have hr1 : 0 < r + 1 := by omega
  rcases Nat.le_total k a with hka | hka
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hka
    induction d with
    | zero => simpa using hbase
    | succ d ih =>
      have ih := ih (by omega)
      set a := k + d
      set c := (T + a) / (r + 1) with hc
      have hrat := bal_ratio hr1 (T + a)
      rw [← hc] at hrat
      have hkla : k ≤ a := by omega
      have hkr : r * k ≤ r * a := Nat.mul_le_mul_left _ hkla
      have hca : c ≤ a := by
        have : c < a + 1 := by
          rw [hc, Nat.div_lt_iff_lt_mul hr1]
          nlinarith
        omega
      have hck : k ≤ c := by
        rw [hc, Nat.le_div_iff_mul_le hr1]
        nlinarith
      have hcpos : 0 < c := by omega
      show (a + 1) * b ≤ bal (r + 1) (T + (a + 1))
      apply Nat.le_of_mul_le_mul_right _ hcpos
      rw [show T + (a + 1) = T + a + 1 by ring, hrat]
      have h3 : (a + 1) * b * c ≤ a * b * (c + 1) := by
        have : b * c ≤ b * a := Nat.mul_le_mul_left _ hca
        nlinarith
      calc (a + 1) * b * c ≤ a * b * (c + 1) := h3
        _ ≤ bal (r + 1) (T + a) * (c + 1) := Nat.mul_le_mul_right _ ih
  · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hka
    have key : ∀ e, e ≤ k → (k - e) * b ≤ bal (r + 1) (T + (k - e)) := by
      intro e
      induction e with
      | zero => intro _; simpa using hbase
      | succ e ih =>
        intro he
        have ih := ih (by omega)
        set a := k - (e + 1) with ha
        have hka1 : k - e = a + 1 := by omega
        rw [hka1] at ih
        set c := (T + a) / (r + 1) with hc
        have hrat := bal_ratio hr1 (T + a)
        rw [← hc] at hrat
        have hac : a ≤ c := by
          rw [hc, Nat.le_div_iff_mul_le hr1]
          have : a ≤ k := by omega
          have : r * a ≤ r * k := Nat.mul_le_mul_left _ this
          nlinarith
        apply Nat.le_of_mul_le_mul_right _ (Nat.succ_pos c)
        rw [← hrat, show T + (a + 1) = T + a + 1 by ring] at *
        have h3 : a * b * (c + 1) ≤ (a + 1) * b * c := by
          have : b * a ≤ b * c := Nat.mul_le_mul_left _ hac
          nlinarith
        calc a * b * (c + 1) ≤ (a + 1) * b * c := h3
          _ ≤ bal (r + 1) (T + a + 1) * c := Nat.mul_le_mul_right _ ih
    have := key d (by omega)
    rwa [show k - d = a by omega] at this



section GroupWalks

variable {n : Nat} {G : Type} [Group G]

private def walkW (E : Fin n → Fin n → G → Prop) (m : Nat) (v : Nat → Fin n) (s : Nat → G) : Prop :=
  ∀ i < m, E (v i) (v (i + 1)) (s i)

private def gainW (m : Nat) (s : Nat → G) : G :=
  ((List.range m).map s).prod

private def pinsOKW (E : Fin n → Fin n → G → Prop) (S : Finset (Fin n)) (z : Fin n → G) (R : Nat) : Prop :=
  ∀ m ≤ R, ∀ v s, walkW E m v s → v 0 ∈ S → v m ∈ S → z (v m) = z (v 0) * gainW m s

private def closedOKW (E : Fin n → Fin n → G → Prop) (radius : Nat) : Prop :=
  ∀ m ≤ radius, ∀ v s, walkW E m v s → v 0 = v m → gainW m s = 1

private abbrev StratW (n : Nat) (G : Type) := List (Finset (Fin n × G)) → Finset (Fin n)

private def histW [DecidableEq G] (ask : StratW n G) (x : Fin n → G) (t : Nat) : List (Finset (Fin n × G)) :=
  (List.range t).foldl (fun hist _ => hist ++ [(ask hist).image (fun u => (u, x u))]) []

private def batchW [DecidableEq G] (ask : StratW n G) (x : Fin n → G) (i : Nat) : Finset (Fin n) :=
  ask (histW ask x i)

private def winW [DecidableEq G] (E : Fin n → Fin n → G → Prop) (ask : StratW n G) (x : Fin n → G)
    (S : Finset (Fin n)) (r : Nat) : Prop :=
  let seen := S ∪ (Finset.range r).biUnion (batchW ask x)
  ∃ u ∈ seen, ∃ v ∈ seen, ∃ g, E u v g ∧ x v ≠ x u * g

private def priceW (bs : List Nat) : Nat × Nat :=
  bs.foldr (fun k (p : Nat × Nat) => ((k + 1) * p.1, max (k * p.1) p.2)) (1, 0)

private lemma priceW_fst_pos (bs : List Nat) : 0 < (priceW bs).1 := by
  induction bs with
  | nil => decide
  | cons k bs ih =>
      dsimp only [priceW, List.foldr] at ih ⊢
      exact Nat.mul_pos (Nat.succ_pos k) ih

private lemma gainW_zero (s : Nat → G) : gainW 0 s = 1 := rfl

private lemma gainW_succ (m : Nat) (s : Nat → G) :
    gainW (m + 1) s = gainW m s * s m := by
  unfold gainW
  rw [List.range_succ, List.map_append, List.prod_append, List.map_singleton, List.prod_singleton]

private lemma gainW_congr (m : Nat) (s1 s2 : Nat → G) (h : ∀ i < m, s1 i = s2 i) :
    gainW m s1 = gainW m s2 := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [gainW_succ, gainW_succ, ih (fun i hi => h i (by omega)), h m (by omega)]

private lemma gainW_add (a d : Nat) (s : Nat → G) :
    gainW (a + d) s = gainW a s * gainW d (fun i => s (a + i)) := by
  induction d with
  | zero => rw [Nat.add_zero, gainW_zero, mul_one]
  | succ d ih =>
      rw [← Nat.add_assoc, gainW_succ, gainW_succ, ih, mul_assoc]

private lemma gainW_concat (m1 m2 : Nat) (s1 s2 : Nat → G) :
    gainW (m1 + m2) (fun i => if i < m1 then s1 i else s2 (i - m1)) = gainW m1 s1 * gainW m2 s2 := by
  rw [gainW_add]
  congr 1
  · exact gainW_congr m1 _ s1 (fun i hi => by simp [hi])
  · exact gainW_congr m2 _ s2 (fun i _ => by
      have hnot : ¬(m1 + i < m1) := by omega
      simp [hnot])

omit [Group G] in
private lemma walkW_slice {E : Fin n → Fin n → G → Prop} {m a b : Nat}
    {v : Nat → Fin n} {s : Nat → G} (hw : walkW E m v s) (hab : a ≤ b) (hbm : b ≤ m) :
    walkW E (b - a) (fun i => v (a + i)) (fun i => s (a + i)) := by
  intro i hi
  dsimp only
  have h1 : a + i < m := by omega
  have h2 : a + (i + 1) = a + i + 1 := by omega
  rw [h2]
  exact hw (a + i) h1

omit [Group G] in
private lemma walkW_concat {E : Fin n → Fin n → G → Prop} {m1 m2 : Nat}
    {v1 v2 : Nat → Fin n} {s1 s2 : Nat → G}
    (hw1 : walkW E m1 v1 s1) (hw2 : walkW E m2 v2 s2) (hmid : v1 m1 = v2 0) :
    walkW E (m1 + m2) (fun i => if i ≤ m1 then v1 i else v2 (i - m1))
      (fun i => if i < m1 then s1 i else s2 (i - m1)) := by
  intro i hi
  by_cases hlt : i < m1
  · have h1 : i ≤ m1 := by omega
    have h2 : i + 1 ≤ m1 := by omega
    simp only [hlt, h1, h2, ↓reduceIte]
    exact hw1 i hlt
  · have h2 : ¬(i + 1 ≤ m1) := by omega
    simp only [hlt, h2, ↓reduceIte]
    by_cases heq : i = m1
    · subst heq
      simp only [le_refl, ↓reduceIte, Nat.sub_self, Nat.add_sub_cancel_left, hmid]
      have hm2 : 0 < m2 := by omega
      exact hw2 0 hm2
    · have h1 : ¬(i ≤ m1) := by omega
      simp only [h1, ↓reduceIte]
      have hidx : i + 1 - m1 = i - m1 + 1 := by omega
      rw [hidx]
      exact hw2 (i - m1) (by omega)

private lemma gainW_rev (m : Nat) (s : Nat → G) :
    gainW m (fun i => (s (m - 1 - i))⁻¹) = (gainW m s)⁻¹ := by
  induction m with
  | zero => simp [gainW_zero]
  | succ m ih =>
      unfold gainW at ih ⊢
      conv_lhs => rw [List.range_succ_eq_map, List.map_cons, List.prod_cons, List.map_map]
      have h0 : m + 1 - 1 - 0 = m := by omega
      rw [h0]
      have htail : (List.map ((fun i => (s (m + 1 - 1 - i))⁻¹) ∘ Nat.succ) (List.range m)).prod =
          (List.map (fun i => (s (m - 1 - i))⁻¹) (List.range m)).prod := by
        congr 1
        refine List.map_congr_left ?_
        intro i hi
        simp only [Function.comp_apply]
        have : m + 1 - 1 - (i + 1) = m - 1 - i := by omega
        rw [this]
      rw [htail, ih]
      have hsuc : (List.map s (List.range (m + 1))).prod = (List.map s (List.range m)).prod * s m := by
        rw [List.range_succ, List.map_append, List.prod_append, List.map_singleton, List.prod_singleton]
      rw [hsuc, mul_inv_rev]

private lemma walkW_rev {E : Fin n → Fin n → G → Prop}
    (hsym : ∀ u v g, E u v g → E v u g⁻¹)
    {m : Nat} {v : Nat → Fin n} {s : Nat → G} (hw : walkW E m v s) :
    walkW E m (fun i => v (m - i)) (fun i => (s (m - 1 - i))⁻¹) := by
  intro i hi
  dsimp only
  have h1 : m - 1 - i < m := by omega
  have h2 : m - 1 - i + 1 = m - i := by omega
  have h3 : m - (i + 1) = m - 1 - i := by omega
  rw [h3, ← h2]
  exact hsym _ _ _ (hw (m - 1 - i) h1)

omit [Group G] in
private lemma histW_zero [DecidableEq G] (ask : StratW n G) (x : Fin n → G) : histW ask x 0 = [] := rfl

omit [Group G] in
private lemma histW_succ [DecidableEq G] (ask : StratW n G) (x : Fin n → G) (t : Nat) :
    histW ask x (t + 1) = histW ask x t ++ [(ask (histW ask x t)).image (fun u => (u, x u))] := by
  unfold histW
  rw [List.range_succ, List.foldl_append]
  rfl

omit [Group G] in
private lemma histW_shift [DecidableEq G] (ask : StratW n G) (x : Fin n → G) (h0 : Finset (Fin n × G))
    (hh0 : h0 = (ask []).image (fun u => (u, x u))) :
    ∀ t : Nat, histW ask x (t + 1) = h0 :: histW (fun rest => ask (h0 :: rest)) x t := by
  intro t
  induction t with
  | zero =>
      rw [histW_succ, histW_zero, histW_zero, List.nil_append, hh0]
  | succ t ih =>
      rw [histW_succ, ih, histW_succ, List.cons_append]

omit [Group G] in
private lemma seen_succ [DecidableEq G] (ask : StratW n G) (x : Fin n → G) (S : Finset (Fin n)) (r : Nat) :
    S ∪ (Finset.range (r + 1)).biUnion (batchW ask x) =
      (S ∪ batchW ask x 0) ∪ (Finset.range r).biUnion (fun i => batchW ask x (i + 1)) := by
  ext w
  simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_range]
  constructor
  · rintro (hw | ⟨i, hi, hw⟩)
    · exact Or.inl (Or.inl hw)
    · cases i with
      | zero => exact Or.inl (Or.inr hw)
      | succ j => exact Or.inr ⟨j, by omega, hw⟩
  · rintro ((hw | hw) | ⟨j, hj, hw⟩)
    · exact Or.inl hw
    · exact Or.inr ⟨0, Nat.succ_pos r, hw⟩
    · exact Or.inr ⟨j + 1, by omega, hw⟩

private lemma telescope_contra (k : Nat) (x : Fin n → G) (v : Nat → Fin n) (s : Nat → G)
    (t : Nat → Nat) (ht0 : t 0 = 0) (htmono : ∀ j < k, t j ≤ t (j + 1))
    (hfail : x (v (t k)) ≠ x (v 0) * gainW (t k) s) :
    ∃ j < k, x (v (t (j + 1))) ≠ x (v (t j)) * gainW (t (j + 1) - t j) (fun i => s (t j + i)) := by
  by_contra hall
  push Not at hall
  have hreach : ∀ r ≤ k, x (v (t r)) = x (v 0) * gainW (t r) s := by
    intro r
    induction r with
    | zero => intro _; rw [ht0, gainW_zero, mul_one]
    | succ r ih =>
        intro hr
        have hstep := hall r (by omega)
        have hprev := ih (by omega)
        have hle := htmono r (by omega)
        have hsplit : gainW (t (r + 1)) s = gainW (t r) s * gainW (t (r + 1) - t r) (fun i => s (t r + i)) := by
          have hadd : t r + (t (r + 1) - t r) = t (r + 1) := by omega
          conv_lhs => rw [← hadd]
          exact gainW_add (t r) (t (r + 1) - t r) s
        rw [hstep, hprev, mul_assoc, ← hsplit]
  exact hfail (hreach k le_rfl)

private noncomputable def zFromAns (S : Finset (Fin n)) (z : Fin n → G)
    (ans : Finset (Fin n × G)) (u : Fin n) : G :=
  open Classical in
  if u ∈ S then z u
  else if h : ∃ g : G, (u, g) ∈ ans then h.choose
  else 1

private lemma zFromAns_eq [DecidableEq G] {S Q : Finset (Fin n)} {z x : Fin n → G}
    (hx : ∀ u ∈ S, x u = z u) (u : Fin n) (hu : u ∈ S ∪ Q) :
    zFromAns S z (Q.image (fun w => (w, x w))) u = x u := by
  classical
  unfold zFromAns
  by_cases huS : u ∈ S
  · simp only [huS, ↓reduceIte]; exact (hx u huS).symm
  · simp only [huS, ↓reduceIte]
    have huQ : u ∈ Q := by
      rcases Finset.mem_union.mp hu with h1 | h2
      · exact (huS h1).elim
      · exact h2
    have hex : ∃ g : G, (u, g) ∈ Q.image (fun w => (w, x w)) :=
      ⟨x u, Finset.mem_image.mpr ⟨u, huQ, rfl⟩⟩
    simp only [hex, ↓reduceDIte]
    have hmem := hex.choose_spec
    rcases Finset.mem_image.mp hmem with ⟨w, _, hw⟩
    have h1 : w = u := congrArg Prod.fst hw
    have h2 : x w = hex.choose := congrArg Prod.snd hw
    rw [← h2, h1]

private def RelR (E : Fin n → Fin n → G → Prop) (R : Nat) (u v : Fin n) (g : G) : Prop :=
  ∃ m ≤ R, ∃ w s, walkW E m w s ∧ w 0 = u ∧ w m = v ∧ gainW m s = g

private lemma RelR_refl (E : Fin n → Fin n → G → Prop) (R : Nat) (u : Fin n) :
    RelR E R u u 1 :=
  ⟨0, Nat.zero_le R, fun _ => u, fun _ => 1, fun _ h => (Nat.not_lt_zero _ h).elim, rfl, rfl, rfl⟩

private lemma RelR_symm {E : Fin n → Fin n → G → Prop}
    (hsym : ∀ u v g, E u v g → E v u g⁻¹) {R : Nat} {u v : Fin n} {g : G}
    (h : RelR E R u v g) : RelR E R v u g⁻¹ := by
  rcases h with ⟨m, hm, w, s, hw, hw0, hwm, hg⟩
  refine ⟨m, hm, fun i => w (m - i), fun i => (s (m - 1 - i))⁻¹, walkW_rev hsym hw, ?_, ?_, ?_⟩
  · simp [hwm]
  · simp [hw0]
  · rw [gainW_rev, hg]

private def RelWalk (E : Fin n → Fin n → G → Prop) (R : Nat) (P : Finset (Fin n))
    (t : Nat) (u : Nat → Fin n) (g : Nat → G) : Prop :=
  (∀ i < t, RelR E R (u i) (u (i + 1)) (g i)) ∧
  (∀ i, 0 < i → i < t → u i ∈ P)

private lemma relWalk_to_walk {E : Fin n → Fin n → G → Prop} {R : Nat} {P : Finset (Fin n)} :
    ∀ (t : Nat) (u : Nat → Fin n) (g : Nat → G),
      RelWalk E R P t u g →
      ∃ m ≤ t * R, ∃ w s, walkW E m w s ∧ w 0 = u 0 ∧ w m = u t ∧ gainW m s = gainW t g := by
  intro t
  induction t with
  | zero =>
      intro u g _
      exact ⟨0, Nat.zero_le _, fun _ => u 0, fun _ => 1, fun _ h => (Nat.not_lt_zero _ h).elim, rfl, rfl, rfl⟩
  | succ t ih =>
      intro u g htw
      have hprev : RelWalk E R P t u g :=
        ⟨fun i hi => htw.1 i (by omega), fun i h0 ht => htw.2 i h0 (by omega)⟩
      rcases ih u g hprev with ⟨m1, hm1, w1, s1, hw1, hw10, hw1m, hg1⟩
      rcases htw.1 t (by omega) with ⟨m2, hm2, w2, s2, hw2, hw20, hw2m, hg2⟩
      refine ⟨m1 + m2, ?_, fun i => if i ≤ m1 then w1 i else w2 (i - m1),
        fun i => if i < m1 then s1 i else s2 (i - m1),
        walkW_concat hw1 hw2 (hw1m.trans hw20.symm), ?_, ?_, ?_⟩
      · calc m1 + m2 ≤ t * R + R := Nat.add_le_add hm1 hm2
        _ = (t + 1) * R := by ring
      · simp [hw10]
      · by_cases hm2z : m2 = 0
        · subst hm2z; simp [hw1m, hw20.symm.trans hw2m]
        · have hnot : ¬(m1 + m2 ≤ m1) := by omega
          simp [hnot, hw2m]
      · rw [gainW_concat, hg1, hg2, gainW_succ]

private lemma relWalk_rev {E : Fin n → Fin n → G → Prop}
    (hsym : ∀ u v g, E u v g → E v u g⁻¹) {R : Nat} {P : Finset (Fin n)}
    {t : Nat} {u : Nat → Fin n} {g : Nat → G} (hw : RelWalk E R P t u g) :
    RelWalk E R P t (fun i => u (t - i)) (fun i => (g (t - 1 - i))⁻¹) := by
  constructor
  · intro i hi
    dsimp only
    have h1 : t - 1 - i < t := by omega
    have h2 : t - 1 - i + 1 = t - i := by omega
    have h3 : t - (i + 1) = t - 1 - i := by omega
    rw [h3, ← h2]
    exact RelR_symm hsym (hw.1 (t - 1 - i) h1)
  · intro i h0 ht
    exact hw.2 (t - i) (by omega) (by omega)

private lemma relWalk_concat {E : Fin n → Fin n → G → Prop} {R : Nat} {P : Finset (Fin n)}
    {t1 t2 : Nat} {u1 u2 : Nat → Fin n} {g1 g2 : Nat → G}
    (hw1 : RelWalk E R P t1 u1 g1) (hw2 : RelWalk E R P t2 u2 g2)
    (hmid : u1 t1 = u2 0) (hmidP : t1 = 0 ∨ t2 = 0 ∨ u1 t1 ∈ P) :
    RelWalk E R P (t1 + t2) (fun i => if i ≤ t1 then u1 i else u2 (i - t1))
      (fun i => if i < t1 then g1 i else g2 (i - t1)) := by
  constructor
  · intro i hi
    by_cases hlt : i < t1
    · have h1 : i ≤ t1 := by omega
      have h2 : i + 1 ≤ t1 := by omega
      simp only [hlt, h1, h2, ↓reduceIte]
      exact hw1.1 i hlt
    · have h2 : ¬(i + 1 ≤ t1) := by omega
      simp only [hlt, h2, ↓reduceIte]
      by_cases heq : i = t1
      · subst heq
        simp only [le_refl, ↓reduceIte, Nat.sub_self, Nat.add_sub_cancel_left, hmid]
        exact hw2.1 0 (by omega)
      · have h1 : ¬(i ≤ t1) := by omega
        simp only [h1, ↓reduceIte]
        have hidx : i + 1 - t1 = i - t1 + 1 := by omega
        rw [hidx]
        exact hw2.1 (i - t1) (by omega)
  · intro i h0 hi
    by_cases hlt : i < t1
    · have hle : i ≤ t1 := by omega
      simp only [hle, ↓reduceIte]
      exact hw1.2 i h0 hlt
    · by_cases heq : i = t1
      · subst heq
        simp only [le_refl, ↓reduceIte]
        rcases hmidP with ht1 | ht2 | hP
        · omega
        · omega
        · exact hP
      · have hnot : ¬(i ≤ t1) := by omega
        simp only [hnot, ↓reduceIte]
        exact hw2.2 (i - t1) (by omega) (by omega)

private lemma relWalk_slice {E : Fin n → Fin n → G → Prop} {R : Nat} {P : Finset (Fin n)}
    {t a b : Nat} {u : Nat → Fin n} {g : Nat → G} (hw : RelWalk E R P t u g)
    (hab : a ≤ b) (hbt : b ≤ t) :
    RelWalk E R P (b - a) (fun i => u (a + i)) (fun i => g (a + i)) := by
  constructor
  · intro i hi
    dsimp only
    have h2 : a + (i + 1) = a + i + 1 := by omega
    rw [h2]
    exact hw.1 (a + i) (by omega)
  · intro i h0 hi
    exact hw.2 (a + i) (by omega) (by omega)

private lemma relWalk_splice {E : Fin n → Fin n → G → Prop} {R : Nat} {P : Finset (Fin n)}
    {t a b : Nat} {u : Nat → Fin n} {g : Nat → G} (hw : RelWalk E R P t u g)
    (hab : a < b) (hbt : b ≤ t) (heq : u a = u b)
    (hloop : gainW (b - a) (fun i => g (a + i)) = 1) :
    ∃ u' g', RelWalk E R P (a + (t - b)) u' g' ∧
      u' 0 = u 0 ∧ u' (a + (t - b)) = u t ∧ gainW (a + (t - b)) g' = gainW t g := by
  have hw2 := relWalk_slice hw hbt le_rfl
  have h1 : RelWalk E R P a u g := by
    constructor
    · intro i hi; exact hw.1 i (by omega)
    · intro i h0 hi; exact hw.2 i h0 (by omega)
  have hmidP : a = 0 ∨ t - b = 0 ∨ u a ∈ P := by
    by_cases ha0 : a = 0
    · exact Or.inl ha0
    · by_cases hbt' : t - b = 0
      · exact Or.inr (Or.inl hbt')
      · exact Or.inr (Or.inr (hw.2 a (by omega) (by omega)))
  have hc := relWalk_concat h1 hw2 (by simp [heq]) hmidP
  refine ⟨fun i => if i ≤ a then u i else u (b + (i - a)),
    fun i => if i < a then g i else g (b + (i - a)), hc, ?_, ?_, ?_⟩
  · simp
  · by_cases htb : t - b = 0
    · have hbtEq : b = t := by omega
      simp [heq, hbtEq]
    · have hnot : ¬(a + (t - b) ≤ a) := by omega
      simp only [hnot, ↓reduceIte, Nat.add_sub_cancel_left]
      have hsum : b + (t - b) = t := by omega
      rw [hsum]
  · rw [gainW_concat a (t - b) g (fun j => g (b + j))]
    have hsplit1 : gainW t g = gainW b g * gainW (t - b) (fun i => g (b + i)) := by
      have hsum : b + (t - b) = t := by omega
      conv_lhs => rw [← hsum]
      exact gainW_add b (t - b) g
    have hsplit2 : gainW b g = gainW a g * gainW (b - a) (fun i => g (a + i)) := by
      have hsum : a + (b - a) = b := by omega
      conv_lhs => rw [← hsum]
      exact gainW_add a (b - a) g
    rw [hsplit1, hsplit2, hloop, mul_one]

private lemma relWalk_closed_gain {E : Fin n → Fin n → G → Prop} {R k : Nat} {P : Finset (Fin n)}
    (hP : P.card ≤ k) (hclosed : closedOKW E (k * R)) :
    ∀ t : Nat, ∀ u g, RelWalk E R P t u g → u 0 ∈ P → u 0 = u t → gainW t g = 1 := by
  intro t
  induction t using Nat.strong_induction_on with
  | ind t ih =>
      intro u g hw hu0 hcl
      by_cases ht0 : t = 0
      · subst ht0; rfl
      · by_cases hdup : ∃ a b : Nat, a < b ∧ b < t ∧ u a = u b
        · rcases hdup with ⟨a, b, hab, hbt, heq⟩
          have hsub := relWalk_slice hw (le_of_lt hab) (le_of_lt hbt)
          have huaP : u a ∈ P := by
            by_cases ha0 : a = 0
            · subst ha0; exact hu0
            · exact hw.2 a (by omega) (by omega)
          have hloop : gainW (b - a) (fun i => g (a + i)) = 1 :=
            ih (b - a) (by omega) _ _ hsub huaP (by simp [Nat.add_sub_cancel' (le_of_lt hab), heq])
          rcases relWalk_splice hw hab (le_of_lt hbt) heq hloop with ⟨u', g', hw', hu0', hut', hgain'⟩
          rw [← hgain']
          exact ih (a + (t - b)) (by omega) u' g' hw' (by rw [hu0']; exact hu0) (by rw [hu0', hut', hcl])
        · push Not at hdup
          have hinj : Function.Injective (fun i : Fin t => (⟨u i.val, by
              by_cases hi0 : i.val = 0
              · rw [hi0]; exact hu0
              · exact hw.2 i.val (by omega) i.isLt⟩ : {v // v ∈ P})) := by
            intro i j hEq
            have huv : u i.val = u j.val := congrArg Subtype.val hEq
            by_contra hne
            have hval : i.val ≠ j.val := fun h => hne (Fin.ext h)
            rcases lt_or_gt_of_ne hval with hlt | hgt
            · exact hdup i.val j.val hlt j.isLt huv
            · exact hdup j.val i.val hgt i.isLt huv.symm
          have htle : t ≤ P.card := by
            have h1 := Fintype.card_le_of_injective _ hinj
            rw [Fintype.card_fin, Fintype.card_coe] at h1
            exact h1
          rcases relWalk_to_walk t u g hw with ⟨m, hm, w, s, hwm, hw0, hwend, hgw⟩
          rw [← hgw]
          exact hclosed m (le_trans hm (Nat.mul_le_mul_right R (le_trans htle hP))) w s hwm
            (hw0.trans (hcl.trans hwend.symm))

private lemma relWalk_pins_gain {E : Fin n → Fin n → G → Prop} {R k : Nat}
    {S P : Finset (Fin n)} {z : Fin n → G}
    (hP : P.card ≤ k) (hpins : pinsOKW E S z ((k + 1) * R)) (hclosed : closedOKW E (k * R)) :
    ∀ t : Nat, ∀ u g, RelWalk E R P t u g → u 0 ∈ S → u t ∈ S → z (u t) = z (u 0) * gainW t g := by
  intro t
  induction t using Nat.strong_induction_on with
  | ind t ih =>
      intro u g hw hu0 hut
      by_cases ht0 : t = 0
      · subst ht0; rw [gainW_zero, mul_one]
      · by_cases hdup : ∃ a b : Nat, 0 < a ∧ a < b ∧ b < t ∧ u a = u b
        · rcases hdup with ⟨a, b, ha0, hab, hbt, heq⟩
          have hsub := relWalk_slice hw (le_of_lt hab) (le_of_lt hbt)
          have huaP : u a ∈ P := hw.2 a ha0 (by omega)
          have hloop : gainW (b - a) (fun i => g (a + i)) = 1 :=
            relWalk_closed_gain hP hclosed (b - a) _ _ hsub huaP
              (by simp [Nat.add_sub_cancel' (le_of_lt hab), heq])
          rcases relWalk_splice hw hab (le_of_lt hbt) heq hloop with ⟨u', g', hw', hu0', hut', hgain'⟩
          rw [← hgain', ← hu0', ← hut']
          exact ih (a + (t - b)) (by omega) u' g' hw' (by rw [hu0']; exact hu0) (by rw [hut']; exact hut)
        · push Not at hdup
          have hinj : Function.Injective (fun i : Fin (t - 1) =>
              (⟨u (i.val + 1), hw.2 (i.val + 1) (Nat.succ_pos _) (by omega)⟩ : {v // v ∈ P})) := by
            intro i j hEq
            have huv : u (i.val + 1) = u (j.val + 1) := congrArg Subtype.val hEq
            by_contra hne
            have hval : i.val ≠ j.val := fun h => hne (Fin.ext h)
            rcases lt_or_gt_of_ne hval with hlt | hgt
            · exact hdup (i.val + 1) (j.val + 1) (Nat.succ_pos _) (by omega) (by omega) huv
            · exact hdup (j.val + 1) (i.val + 1) (Nat.succ_pos _) (by omega) (by omega) huv.symm
          have htle : t - 1 ≤ P.card := by
            have h1 := Fintype.card_le_of_injective _ hinj
            rw [Fintype.card_fin, Fintype.card_coe] at h1
            exact h1
          have htk : t ≤ k + 1 := by omega
          rcases relWalk_to_walk t u g hw with ⟨m, hm, w, s, hwm, hw0, hwend, hgw⟩
          rw [← hgw, ← hw0, ← hwend]
          exact hpins m (le_trans hm (Nat.mul_le_mul_right R htk)) w s hwm
            (by rw [hw0]; exact hu0) (by rw [hwend]; exact hut)

private lemma exists_extension {E : Fin n → Fin n → G → Prop}
    (hsym : ∀ u v g, E u v g → E v u g⁻¹)
    {S Q : Finset (Fin n)} {z : Fin n → G} {R k : Nat}
    (hQ : Q.card ≤ k) (hpins : pinsOKW E S z ((k + 1) * R)) (hclosed : closedOKW E (k * R)) :
    ∃ z' : Fin n → G, (∀ u ∈ S, z' u = z u) ∧ pinsOKW E (S ∪ Q) z' R := by
  classical
  let P : Finset (Fin n) := Q \ S
  have hPcard : P.card ≤ k := le_trans (Finset.card_le_card Finset.sdiff_subset) hQ
  let ReachS (v : Fin n) (val : G) : Prop :=
    ∃ s ∈ S, ∃ t u g, RelWalk E R P t u g ∧ u 0 = s ∧ u t = v ∧ val = z s * gainW t g
  have hReachS_uniq : ∀ v val1 val2, v ∈ P → ReachS v val1 → ReachS v val2 → val1 = val2 := by
    intro v val1 val2 hvP ⟨s1, hs1, t1, u1, g1, hw1, hu10, hu1t, hv1⟩
      ⟨s2, hs2, t2, u2, g2, hw2, hu20, hu2t, hv2⟩
    have hw2r := relWalk_rev hsym hw2
    have hmid : u1 t1 = (fun i => u2 (t2 - i)) 0 := by simp [hu1t, hu2t]
    have hmidP : t1 = 0 ∨ t2 = 0 ∨ u1 t1 ∈ P := Or.inr (Or.inr (by rw [hu1t]; exact hvP))
    have hcat := relWalk_concat hw1 hw2r hmid hmidP
    have hpin := relWalk_pins_gain hPcard hpins hclosed (t1 + t2) _ _ hcat
      (by simp [hu10, hs1]) (by
        by_cases ht2 : t2 = 0
        · subst ht2; simp [hu1t, ← hu2t, hu20, hs2]
        · have hnot : ¬(t1 + t2 ≤ t1) := by omega
          simp [hnot, hu20, hs2])
    have hu_start : (if (0 : Nat) ≤ t1 then u1 0 else u2 (t2 - (0 - t1))) = s1 := by simp [hu10]
    have hu_end : (if t1 + t2 ≤ t1 then u1 (t1 + t2) else u2 (t2 - (t1 + t2 - t1))) = s2 := by
      by_cases ht2 : t2 = 0
      · subst ht2; simp [hu1t, ← hu2t, hu20]
      · have hnot : ¬(t1 + t2 ≤ t1) := by omega
        simp [hnot, hu20]
    rw [hu_start, hu_end, gainW_concat t1 t2 g1 (fun j => (g2 (t2 - 1 - j))⁻¹), gainW_rev] at hpin
    rw [hv1, hv2, hpin]
    group
  let ReachP (a b : Fin n) (val : G) : Prop :=
    ∃ t u g, RelWalk E R P t u g ∧ u 0 = a ∧ u t = b ∧ val = gainW t g
  have hReachP_uniq : ∀ a b val1 val2, a ∈ P → b ∈ P → ReachP a b val1 → ReachP a b val2 → val1 = val2 := by
    intro a b val1 val2 haP hbP ⟨t1, u1, g1, hw1, hu10, hu1t, hv1⟩
      ⟨t2, u2, g2, hw2, hu20, hu2t, hv2⟩
    have hw2r := relWalk_rev hsym hw2
    have hcat := relWalk_concat hw1 hw2r (by simp [hu1t, hu2t]) (Or.inr (Or.inr (by rw [hu1t]; exact hbP)))
    have hcl := relWalk_closed_gain hPcard hclosed (t1 + t2) _ _ hcat
      (by simp [hu10, haP]) (by
        by_cases ht2 : t2 = 0
        · subst ht2; simp [hu10, hu1t, ← hu2t, hu20]
        · have hnot : ¬(t1 + t2 ≤ t1) := by omega
          simp [hnot, hu10, hu20])
    rw [gainW_concat t1 t2 g1 (fun j => (g2 (t2 - 1 - j))⁻¹), gainW_rev] at hcl
    rw [hv1, hv2]
    exact eq_of_mul_inv_eq_one hcl
  let comp (v : Fin n) : Finset (Fin n) := P.filter (fun w => ∃ val, ReachP w v val)
  have hReachP_refl : ∀ v, ReachP v v 1 := fun v =>
    ⟨0, fun _ => v, fun _ => 1, ⟨fun _ h => (Nat.not_lt_zero _ h).elim, fun _ _ h => (Nat.not_lt_zero _ h).elim⟩,
      rfl, rfl, rfl⟩
  have hReachP_symm : ∀ a b val, ReachP a b val → ReachP b a val⁻¹ := by
    intro a b val ⟨t, u, g, hw, h0, ht, hval⟩
    exact ⟨t, fun i => u (t - i), fun i => (g (t - 1 - i))⁻¹, relWalk_rev hsym hw,
      by simp [ht], by simp [h0], by rw [gainW_rev, hval]⟩
  have hReachP_trans : ∀ a b c v1 v2, b ∈ P → ReachP a b v1 → ReachP b c v2 → ReachP a c (v1 * v2) := by
    intro a b c v1 v2 hbP ⟨t1, u1, g1, hw1, hu10, hu1t, hv1⟩ ⟨t2, u2, g2, hw2, hu20, hu2t, hv2⟩
    refine ⟨t1 + t2, fun i => if i ≤ t1 then u1 i else u2 (i - t1),
      fun i => if i < t1 then g1 i else g2 (i - t1),
      relWalk_concat hw1 hw2 (hu1t.trans hu20.symm) (Or.inr (Or.inr (by rw [hu1t]; exact hbP))),
      by simp [hu10], ?_, by rw [gainW_concat, hv1, hv2]⟩
    by_cases ht2 : t2 = 0
    · subst ht2; simp [hu1t, ← hu20, hu2t]
    · have hnot : ¬(t1 + t2 ≤ t1) := by omega
      simp [hnot, hu2t]
  have hcomp_ne : ∀ v ∈ P, (comp v).Nonempty := fun v hvP =>
    ⟨v, Finset.mem_filter.mpr ⟨hvP, ⟨1, hReachP_refl v⟩⟩⟩
  have hcomp_eq : ∀ u v g, u ∈ P → v ∈ P → RelR E R u v g → comp u = comp v := by
    intro u v g huP hvP hrel
    have hstep : ReachP u v g :=
      ⟨1, fun i => if i = 0 then u else v, fun _ => g,
        ⟨fun i hi => by dsimp only; have hi0 : i = 0 := (by omega); subst hi0; simpa using hrel,
          fun i h0 h1 => by omega⟩,
        rfl, rfl, by rw [gainW_succ, gainW_zero, one_mul]⟩
    ext w
    simp only [comp, Finset.mem_filter]
    constructor
    · rintro ⟨hwP, val, hwu⟩
      exact ⟨hwP, val * g, hReachP_trans w u v val g huP hwu hstep⟩
    · rintro ⟨hwP, val, hwv⟩
      exact ⟨hwP, val * g⁻¹, hReachP_trans w v u val g⁻¹ hvP hwv (hReachP_symm u v g hstep)⟩
  let rep (v : Fin n) : Fin n :=
    if h : (comp v).Nonempty then (comp v).min' h else v
  have hrep_spec : ∀ v ∈ P, rep v ∈ P ∧ ∃ val, ReachP (rep v) v val := by
    intro v hvP
    have hne := hcomp_ne v hvP
    have hmem : rep v ∈ comp v := by
      dsimp only [rep]; simp only [hne, ↓reduceDIte]; exact Finset.min'_mem _ hne
    exact Finset.mem_filter.mp hmem
  let z' : Fin n → G := fun v =>
    if v ∈ S then z v
    else if hvP : v ∈ P then
      if hS : ∃ val, ReachS v val then hS.choose
      else (hrep_spec v hvP).2.choose
    else 1
  have hz'_S : ∀ v ∈ S, z' v = z v := fun v hv => by dsimp only [z']; simp only [hv, ↓reduceIte]
  have hz'_ReachS : ∀ v val, v ∈ P → ReachS v val → z' v = val := by
    intro v val hvP hR
    have hvS : v ∉ S := (Finset.mem_sdiff.mp hvP).2
    dsimp only [z']
    simp only [hvS, ↓reduceIte, hvP, ↓reduceDIte]
    have hex : ∃ w, ReachS v w := ⟨val, hR⟩
    simp only [hex, ↓reduceDIte]
    exact hReachS_uniq v hex.choose val hvP hex.choose_spec hR
  have hz'_ReachP : ∀ v val, v ∈ P → (¬∃ w, ReachS v w) → ReachP (rep v) v val → z' v = val := by
    intro v val hvP hnoS hRP
    have hvS : v ∉ S := (Finset.mem_sdiff.mp hvP).2
    dsimp only [z']
    simp only [hvS, ↓reduceIte, hvP, hnoS, ↓reduceDIte]
    exact hReachP_uniq (rep v) v (hrep_spec v hvP).2.choose val (hrep_spec v hvP).1 hvP
      (hrep_spec v hvP).2.choose_spec hRP
  refine ⟨z', hz'_S, ?_⟩
  intro m hm w s hw hw0 hwm
  set u := w 0
  set v := w m
  set g := gainW m s
  have hrel : RelR E R u v g := ⟨m, hm, w, s, hw, rfl, rfl, rfl⟩
  have hstep1 : ∀ a b c, RelR E R a b c → RelWalk E R P 1 (fun i => if i = 0 then a else b) (fun _ => c) := by
    intro a b c hrc
    exact ⟨fun i hi => by dsimp only; have hi0 : i = 0 := (by omega); subst hi0; simpa using hrc, fun i h0 h1 => by omega⟩
  by_cases huS : u ∈ S
  · by_cases hvS : v ∈ S
    · rw [hz'_S u huS, hz'_S v hvS]
      exact hpins m (le_trans hm (Nat.le_mul_of_pos_left R (Nat.succ_pos k))) w s hw huS hvS
    · have hvP : v ∈ P := by
        rcases Finset.mem_union.mp hwm with h1 | h2
        · exact (hvS h1).elim
        · exact Finset.mem_sdiff.mpr ⟨h2, hvS⟩
      have hRS : ReachS v (z u * g) :=
        ⟨u, huS, 1, fun i => if i = 0 then u else v, fun _ => g, hstep1 u v g hrel,
          rfl, rfl, by rw [gainW_succ, gainW_zero, one_mul]⟩
      rw [hz'_S u huS, hz'_ReachS v (z u * g) hvP hRS]
  · have huP : u ∈ P := by
      rcases Finset.mem_union.mp hw0 with h1 | h2
      · exact (huS h1).elim
      · exact Finset.mem_sdiff.mpr ⟨h2, huS⟩
    by_cases hvS : v ∈ S
    · have hRS : ReachS u (z v * g⁻¹) :=
        ⟨v, hvS, 1, fun i => if i = 0 then v else u, fun _ => g⁻¹, hstep1 v u g⁻¹ (RelR_symm hsym hrel),
          rfl, rfl, by rw [gainW_succ, gainW_zero, one_mul]⟩
      rw [hz'_S v hvS, hz'_ReachS u (z v * g⁻¹) huP hRS]
      group
    · have hvP : v ∈ P := by
        rcases Finset.mem_union.mp hwm with h1 | h2
        · exact (hvS h1).elim
        · exact Finset.mem_sdiff.mpr ⟨h2, hvS⟩
      by_cases huR : ∃ val, ReachS u val
      · rcases huR with ⟨val, s0, hs0, t1, u1, g1, hw1, hu10, hu1t, hval⟩
        have hcat := relWalk_concat hw1 (hstep1 u v g hrel) hu1t (Or.inr (Or.inr (by rw [hu1t]; exact huP)))
        have hvR : ReachS v (val * g) :=
          ⟨s0, hs0, t1 + 1, _, _, hcat, by simp [hu10],
            by have hnot : ¬(t1 + 1 ≤ t1) := (by omega); simp [hnot],
            by rw [gainW_concat t1 1 g1 (fun _ => g), gainW_succ, gainW_zero, one_mul, hval, mul_assoc]⟩
        rw [hz'_ReachS u val huP ⟨s0, hs0, t1, u1, g1, hw1, hu10, hu1t, hval⟩,
          hz'_ReachS v (val * g) hvP hvR]
      · have hvNo : ¬∃ val, ReachS v val := by
          rintro ⟨val, s0, hs0, t1, u1, g1, hw1, hu10, hu1t, hval⟩
          have hcat := relWalk_concat hw1 (hstep1 v u g⁻¹ (RelR_symm hsym hrel)) hu1t
            (Or.inr (Or.inr (by rw [hu1t]; exact hvP)))
          exact huR ⟨val * g⁻¹, s0, hs0, t1 + 1, _, _, hcat, by simp [hu10],
            by have hnot : ¬(t1 + 1 ≤ t1) := (by omega); simp [hnot],
            by rw [gainW_concat t1 1 g1 (fun _ => g⁻¹), gainW_succ, gainW_zero, one_mul, hval, mul_assoc]⟩
        have hreq : rep u = rep v := by
          dsimp only [rep]
          rw [hcomp_eq u v g huP hvP hrel]
          simp only [hcomp_ne v hvP, ↓reduceDIte]
        rcases (hrep_spec u huP).2 with ⟨val, hru⟩
        have hstepP : ReachP u v g := ⟨1, fun i => if i = 0 then u else v, fun _ => g, hstep1 u v g hrel,
          rfl, rfl, by rw [gainW_succ, gainW_zero, one_mul]⟩
        have hrv : ReachP (rep v) v (val * g) := by
          rw [← hreq]
          exact hReachP_trans (rep u) u v val g huP hru hstepP
        rw [hz'_ReachP u val huP huR hru, hz'_ReachP v (val * g) hvP hvNo hrv]

private lemma main_258 [DecidableEq G] (E : Fin n → Fin n → G → Prop)
    (hsym : ∀ u v g, E u v g → E v u g⁻¹) (bs : List Nat) :
    ∀ (S : Finset (Fin n)) (z : Fin n → G),
      (∃ ask : StratW n G, ∀ x : Fin n → G, (∀ u ∈ S, x u = z u) →
        (∀ i : Fin bs.length, (batchW ask x i.val).card ≤ bs[i.val]'i.isLt) ∧
        winW E ask x S bs.length) ↔
      ¬ pinsOKW E S z (priceW bs).1 ∨ ¬ closedOKW E (priceW bs).2 := by
  induction bs with
  | nil =>
      intro S z
      have hcl0 : closedOKW E 0 := by
        intro m hm _ _ _ _
        have hm0 : m = 0 := by omega
        subst hm0; rfl
      constructor
      · rintro ⟨ask, hask⟩
        left
        intro hpins
        have hw0 := (hask z (fun _ _ => rfl)).2
        unfold winW at hw0
        simp only [List.length_nil, Finset.range_zero, Finset.biUnion_empty, Finset.union_empty] at hw0
        rcases hw0 with ⟨u, hu, v, hv, g, hE, hne⟩
        have heq := hpins 1 le_rfl (fun i => if i = 0 then u else v) (fun _ => g)
          (fun i hi => by dsimp only; have hi0 : i = 0 := (by omega); subst hi0; simpa using hE)
          (by simpa using hu) (by simpa using hv)
        rw [show (1 : Nat) = 0 + 1 from rfl, gainW_succ, gainW_zero, one_mul] at heq
        exact hne heq
      · rintro (hnp | hnc)
        · refine ⟨fun _ => ∅, fun x hx => ⟨fun i => (Nat.not_lt_zero _ i.isLt).elim, ?_⟩⟩
          unfold pinsOKW at hnp
          push Not at hnp
          rcases hnp with ⟨m, hm, v, s, hw, hv0, hvm, hne⟩
          have hm1 : m = 1 := by
            by_cases hm0 : m = 0
            · subst hm0; rw [gainW_zero, mul_one] at hne; exact (hne rfl).elim
            · change m ≤ 1 at hm; omega
          subst hm1
          rw [show (1 : Nat) = 0 + 1 from rfl, gainW_succ, gainW_zero, one_mul] at hne
          refine ⟨v 0, by simp [hv0], v 1, by simp [hvm], s 0, hw 0 (Nat.zero_lt_one), ?_⟩
          rw [hx (v 0) hv0, hx (v 1) hvm]
          exact hne
        · exact (hnc hcl0).elim
  | cons k bs ih =>
      intro S z
      let R := (priceW bs).1
      let C := (priceW bs).2
      have hp_eq : priceW (k :: bs) = ((k + 1) * R, max (k * R) C) := rfl
      rw [hp_eq]
      dsimp only
      constructor
      · rintro ⟨ask, hask⟩
        by_contra hok
        push Not at hok
        rcases hok with ⟨hpins, hclosed⟩
        have hcl_kR : closedOKW E (k * R) := fun m hm => hclosed m (le_trans hm (le_max_left _ _))
        have hcl_C : closedOKW E C := fun m hm => hclosed m (le_trans hm (le_max_right _ _))
        let Q := ask []
        have hQcard : Q.card ≤ k := (hask z (fun _ _ => rfl)).1 ⟨0, Nat.succ_pos _⟩
        rcases exists_extension hsym hQcard hpins hcl_kR with ⟨z', hz'S, hpins'⟩
        let h0 : Finset (Fin n × G) := Q.image (fun u => (u, z' u))
        let ask' : StratW n G := fun rest => ask (h0 :: rest)
        have hwin' : ∃ ask' : StratW n G, ∀ x : Fin n → G, (∀ u ∈ S ∪ Q, x u = z' u) →
            (∀ i : Fin bs.length, (batchW ask' x i.val).card ≤ bs[i.val]'i.isLt) ∧
            winW E ask' x (S ∪ Q) bs.length := by
          refine ⟨ask', fun x hx => ?_⟩
          have hxS : ∀ u ∈ S, x u = z u := fun u hu =>
            (hx u (Finset.mem_union_left Q hu)).trans (hz'S u hu)
          have hh0 : h0 = (ask []).image (fun u => (u, x u)) := by
            dsimp only [h0, Q]
            refine Finset.image_congr ?_
            intro u hu
            dsimp only
            rw [hx u (Finset.mem_union_right S hu)]
          have hbatch_eq : ∀ i : Nat, batchW ask x (i + 1) = batchW ask' x i := by
            intro i
            unfold batchW
            rw [histW_shift ask x h0 hh0 i]
          rcases hask x hxS with ⟨hcard, hwin⟩
          constructor
          · intro i
            rw [← hbatch_eq i.val]
            exact hcard ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩
          · unfold winW at hwin ⊢
            dsimp only [List.length_cons] at hwin
            rw [seen_succ] at hwin
            have hseen_eq : (S ∪ batchW ask x 0) ∪ (Finset.range bs.length).biUnion (fun i => batchW ask x (i + 1)) =
                (S ∪ Q) ∪ (Finset.range bs.length).biUnion (batchW ask' x) := by
              congr 1
              refine Finset.biUnion_congr rfl ?_
              intro i _
              exact hbatch_eq i
            rw [hseen_eq] at hwin
            exact hwin
        rcases (ih (S ∪ Q) z').mp hwin' with hnp' | hnc'
        · exact hnp' hpins'
        · exact hnc' hcl_C
      · intro hbad
        classical
        by_cases hclC : ¬ closedOKW E C
        · rcases (ih S z).mpr (Or.inr hclC) with ⟨ask', hask'⟩
          let ask : StratW n G := fun hist =>
            match hist with
            | [] => ∅
            | _ :: rest => ask' rest
          refine ⟨ask, fun x hx => ?_⟩
          have hh0 : (∅ : Finset (Fin n × G)) = (ask []).image (fun u => (u, x u)) := by simp [ask]
          have hbatch_eq : ∀ i : Nat, batchW ask x (i + 1) = batchW ask' x i := by
            intro i
            unfold batchW
            rw [histW_shift ask x ∅ hh0 i]
          rcases hask' x hx with ⟨hcard', hwin'⟩
          constructor
          · rintro ⟨iv, hiv⟩
            cases iv with
            | zero => simp [batchW, histW, ask]
            | succ j =>
                rw [hbatch_eq j]
                exact hcard' ⟨j, Nat.lt_of_succ_lt_succ hiv⟩
          · unfold winW at hwin' ⊢
            dsimp only [List.length_cons]
            rw [seen_succ]
            have hseen_eq : (S ∪ batchW ask x 0) ∪ (Finset.range bs.length).biUnion (fun i => batchW ask x (i + 1)) =
                S ∪ (Finset.range bs.length).biUnion (batchW ask' x) := by
              have h0e : batchW ask x 0 = ∅ := rfl
              rw [h0e, Finset.union_empty]
              congr 1
              refine Finset.biUnion_congr rfl ?_
              intro i _
              exact hbatch_eq i
            rw [hseen_eq]
            exact hwin'
        · have hRpos : 0 < R := priceW_fst_pos bs
          have hQ_exists : ∃ Q : Finset (Fin n), Q.card ≤ k ∧
              ∀ z' : Fin n → G, (∀ u ∈ S, z' u = z u) → ¬ pinsOKW E (S ∪ Q) z' R := by
            rcases hbad with hnp | hnc
            · unfold pinsOKW at hnp
              push Not at hnp
              rcases hnp with ⟨m, hm, v, s, hw, hv0, hvm, hne⟩
              let t : Nat → Nat := fun j => if j ≤ k then min (j * R) m else m
              let Q : Finset (Fin n) := (Finset.range k).image (fun j => v (min ((j + 1) * R) m))
              refine ⟨Q, le_trans Finset.card_image_le (by rw [Finset.card_range]), ?_⟩
              intro z' hz' hpins'
              have ht0 : t 0 = 0 := by simp [t]
              have htk1 : t (k + 1) = m := by simp [t]
              have htmono : ∀ j < k + 1, t j ≤ t (j + 1) := by
                intro j hj
                dsimp only [t]
                have hjle : j ≤ k := by omega
                simp only [hjle, ↓reduceIte]
                by_cases hj1 : j + 1 ≤ k
                · simp only [hj1, ↓reduceIte]
                  exact min_le_min_right m (Nat.mul_le_mul_right R (by omega))
                · simp only [hj1, ↓reduceIte]
                  exact min_le_right _ _
              have hfail : z' (v (t (k + 1))) ≠ z' (v 0) * gainW (t (k + 1)) s := by
                rw [htk1, hz' (v 0) hv0, hz' (v m) hvm]
                exact hne
              rcases telescope_contra (k + 1) z' v s t ht0 htmono hfail with ⟨j, hj, hseg⟩
              have hlen : t (j + 1) - t j ≤ R := by
                dsimp only [t]
                have hjle : j ≤ k := by omega
                simp only [hjle, ↓reduceIte]
                by_cases hj1 : j + 1 ≤ k
                · simp only [hj1, ↓reduceIte]
                  have h1' : (j + 1) * R = j * R + R := by ring
                  omega
                · simp only [hj1, ↓reduceIte]
                  have hjEq : j = k := by omega
                  rw [hjEq]
                  have h1' : (k + 1) * R = k * R + R := by ring
                  omega
              have hmem : ∀ r ≤ k + 1, v (t r) ∈ S ∪ Q := by
                intro r hr
                by_cases hr0 : r = 0
                · subst hr0; rw [ht0]; exact Finset.mem_union_left Q hv0
                · by_cases hrk : r = k + 1
                  · subst hrk; rw [htk1]; exact Finset.mem_union_left Q hvm
                  · refine Finset.mem_union_right S ?_
                    refine Finset.mem_image.mpr ⟨r - 1, Finset.mem_range.mpr (by omega), ?_⟩
                    have hle : r ≤ k := by omega
                    have hsub : r - 1 + 1 = r := by omega
                    simp [t, hle, hsub]
              have hw_seg := walkW_slice hw (htmono j hj) (by
                dsimp only [t]; split_ifs <;> omega)
              have hok := hpins' (t (j + 1) - t j) hlen _ _ hw_seg
                (by simpa using hmem j (by omega))
                (by
                  have hsum : t j + (t (j + 1) - t j) = t (j + 1) := by have := htmono j hj; omega
                  simpa [hsum] using hmem (j + 1) (by omega))
              have hsum : t j + (t (j + 1) - t j) = t (j + 1) := by have := htmono j hj; omega
              simp only [Nat.add_zero, hsum] at hok
              exact hseg hok
            · push Not at hclC
              have hnc_kR : ¬ closedOKW E (k * R) := by
                intro hkR
                apply hnc
                intro m hm
                rcases le_max_iff.mp hm with h1 | h2
                · exact hkR m h1
                · exact hclC m h2
              unfold closedOKW at hnc_kR
              push Not at hnc_kR
              rcases hnc_kR with ⟨m, hm, v, s, hw, hcl, hne⟩
              have hkpos : 0 < k := by
                by_contra hk0
                have hkeq : k = 0 := by omega
                subst hkeq
                have hm0 : m = 0 := by omega
                subst hm0
                exact hne rfl
              let t : Nat → Nat := fun j => if j < k then min (j * R) m else m
              let Q : Finset (Fin n) := (Finset.range k).image (fun j => v (min (j * R) m))
              refine ⟨Q, le_trans Finset.card_image_le (by rw [Finset.card_range]), ?_⟩
              intro z' _ hpins'
              have ht0 : t 0 = 0 := by simp [t, hkpos]
              have htk : t k = m := by simp [t]
              have htmono : ∀ j < k, t j ≤ t (j + 1) := by
                intro j hj
                dsimp only [t]
                simp only [hj, ↓reduceIte]
                by_cases hj1 : j + 1 < k
                · simp only [hj1, ↓reduceIte]
                  exact min_le_min_right m (Nat.mul_le_mul_right R (by omega))
                · simp only [hj1, ↓reduceIte]
                  exact min_le_right _ _
              have hfail : z' (v (t k)) ≠ z' (v 0) * gainW (t k) s := by
                rw [htk, ← hcl]
                intro heq
                have h1 : gainW m s = 1 := mul_left_cancel (heq.symm.trans (mul_one _).symm)
                exact hne h1
              rcases telescope_contra k z' v s t ht0 htmono hfail with ⟨j, hj, hseg⟩
              have hlen : t (j + 1) - t j ≤ R := by
                dsimp only [t]
                simp only [hj, ↓reduceIte]
                by_cases hj1 : j + 1 < k
                · simp only [hj1, ↓reduceIte]
                  have : (j + 1) * R = j * R + R := by ring
                  omega
                · simp only [hj1, ↓reduceIte]
                  have hjEq : j + 1 = k := by omega
                  have : k * R = j * R + R := by rw [← hjEq]; ring
                  omega
              have hmem : ∀ r ≤ k, v (t r) ∈ S ∪ Q := by
                intro r hr
                refine Finset.mem_union_right S ?_
                by_cases hrk : r < k
                · refine Finset.mem_image.mpr ⟨r, Finset.mem_range.mpr hrk, ?_⟩
                  simp [t, hrk]
                · have hreq : r = k := by omega
                  subst hreq
                  rw [htk, ← hcl]
                  refine Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr hkpos, ?_⟩
                  simp
              have hw_seg := walkW_slice hw (htmono j hj) (by
                dsimp only [t]; split_ifs <;> omega)
              have hok := hpins' (t (j + 1) - t j) hlen _ _ hw_seg
                (by simpa using hmem j (by omega))
                (by
                  have hsum : t j + (t (j + 1) - t j) = t (j + 1) := by have := htmono j hj; omega
                  simpa [hsum] using hmem (j + 1) (by omega))
              have hsum : t j + (t (j + 1) - t j) = t (j + 1) := by have := htmono j hj; omega
              simp only [Nat.add_zero, hsum] at hok
              exact hseg hok
          rcases hQ_exists with ⟨Q, hQcard, hQbad⟩
          have hsub : ∀ ans : Finset (Fin n × G),
              ∃ ask' : StratW n G, ∀ x : Fin n → G,
                (∀ u ∈ S ∪ Q, x u = zFromAns S z ans u) →
                (∀ i : Fin bs.length, (batchW ask' x i.val).card ≤ bs[i.val]'i.isLt) ∧
                winW E ask' x (S ∪ Q) bs.length := by
            intro ans
            by_cases hag : ∀ u ∈ S, zFromAns S z ans u = z u
            · exact (ih (S ∪ Q) (zFromAns S z ans)).mpr (Or.inl (hQbad _ hag))
            · have : ∀ u ∈ S, zFromAns S z ans u = z u := fun u hu => by
                unfold zFromAns; simp only [hu, ↓reduceIte]
              exact (hag this).elim
          let ask : StratW n G := fun hist =>
            match hist with
            | [] => Q
            | h0 :: rest => (hsub h0).choose rest
          refine ⟨ask, fun x hx => ?_⟩
          let h0 := Q.image (fun u => (u, x u))
          have hh0 : h0 = (ask []).image (fun u => (u, x u)) := rfl
          have hbatch_eq : ∀ i : Nat, batchW ask x (i + 1) = batchW (hsub h0).choose x i := by
            intro i
            unfold batchW
            rw [histW_shift ask x h0 hh0 i]
            rfl
          have hx_z : ∀ u ∈ S ∪ Q, x u = zFromAns S z h0 u := fun u hu =>
            (zFromAns_eq hx u hu).symm
          rcases (hsub h0).choose_spec x hx_z with ⟨hcard', hwin'⟩
          constructor
          · rintro ⟨iv, hiv⟩
            cases iv with
            | zero => simpa [batchW, histW, ask] using hQcard
            | succ j =>
                rw [hbatch_eq j]
                exact hcard' ⟨j, Nat.lt_of_succ_lt_succ hiv⟩
          · unfold winW at hwin' ⊢
            dsimp only [List.length_cons]
            rw [seen_succ]
            have hseen_eq : (S ∪ batchW ask x 0) ∪ (Finset.range bs.length).biUnion (fun i => batchW ask x (i + 1)) =
                (S ∪ Q) ∪ (Finset.range bs.length).biUnion (batchW (hsub h0).choose x) := by
              congr 1
              refine Finset.biUnion_congr rfl ?_
              intro i _
              exact hbatch_eq i
            rw [hseen_eq]
            exact hwin'


lemma bal_one (t : Nat) : bal 1 t = t := by
  unfold bal
  rw [Nat.div_one, Nat.mod_one]
  simp

lemma bal_K' (r T a : Nat) : a * bal r T ≤ bal (r + 1) (T + a) := by
  rcases Nat.eq_zero_or_pos r with h0 | hr
  · subst h0; rw [bal_zero, Nat.zero_add, bal_one]; omega
  · exact bal_K hr T a

private lemma pinsOKW_mono {E : Fin n → Fin n → G → Prop} {S : Finset (Fin n)} {z : Fin n → G}
    {R1 R2 : Nat} (h12 : R1 ≤ R2) (h : pinsOKW E S z R2) : pinsOKW E S z R1 :=
  fun m hm => h m (le_trans hm h12)

private lemma closedOKW_mono {E : Fin n → Fin n → G → Prop}
    {R1 R2 : Nat} (h12 : R1 ≤ R2) (h : closedOKW E R2) : closedOKW E R1 :=
  fun m hm => h m (le_trans hm h12)

private lemma closedOKW_zero (E : Fin n → Fin n → G → Prop) : closedOKW E 0 := by
  intro m hm _ _ _ _
  have hm0 : m = 0 := by omega
  subst hm0; rfl

private lemma adv309 [DecidableEq G] (E : Fin n → Fin n → G → Prop)
    (hsym : ∀ u v g, E u v g → E v u g⁻¹) :
    ∀ (r B : Nat) (S : Finset (Fin n)) (z : Fin n → G),
      (∃ ask : StratW n G, ∀ x : Fin n → G, (∀ u ∈ S, x u = z u) →
        (Finset.range r).sum (fun i => (batchW ask x i).card) ≤ B ∧ winW E ask x S r) →
      ¬ pinsOKW E S z (bal r (B + r)) ∨ ¬ closedOKW E (if r = 0 then 0 else bal r (B + r - 1)) := by
  intro r
  induction r with
  | zero =>
      rintro B S z ⟨ask, hask⟩
      left
      intro hpins
      rw [Nat.add_zero, bal_zero] at hpins
      have hw0 := (hask z (fun _ _ => rfl)).2
      unfold winW at hw0
      simp only [Finset.range_zero, Finset.biUnion_empty, Finset.union_empty] at hw0
      rcases hw0 with ⟨u, hu, v, hv, g, hE, hne⟩
      have heq := hpins 1 le_rfl (fun i => if i = 0 then u else v) (fun _ => g)
        (fun i hi => by dsimp only; have hi0 : i = 0 := (by omega); subst hi0; simpa using hE)
        (by simpa using hu) (by simpa using hv)
      rw [show (1 : Nat) = 0 + 1 from rfl, gainW_succ, gainW_zero, one_mul] at heq
      exact hne heq
  | succ r ih =>
      rintro B S z ⟨ask, hask⟩
      by_contra hok
      push Not at hok
      rcases hok with ⟨hpins, hclosed⟩
      simp only [Nat.succ_ne_zero, if_false] at hclosed
      let Q := ask []
      have hQcard : Q.card ≤ B := by
        have h1 := (hask z (fun _ _ => rfl)).1
        rw [Finset.sum_range_succ'] at h1
        have h0 : batchW ask z 0 = Q := rfl
        rw [h0] at h1
        omega
      set q := Q.card with hq
      set R := bal r (B - q + r) with hR
      have hpq : pinsOKW E S z ((q + 1) * R) := by
        refine pinsOKW_mono ?_ hpins
        have := bal_K' r (B - q + r) (q + 1)
        rw [show B - q + r + (q + 1) = B + (r + 1) by omega] at this
        exact this
      have hcl_qR : closedOKW E (q * R) := by
        refine closedOKW_mono ?_ hclosed
        have := bal_K' r (B - q + r) q
        rw [show B - q + r + q = B + (r + 1) - 1 by omega] at this
        exact this
      have hcl_C : closedOKW E (if r = 0 then 0 else bal r (B - q + r - 1)) := by
        by_cases hr0 : r = 0
        · rw [if_pos hr0]; exact closedOKW_zero E
        · rw [if_neg hr0]
          refine closedOKW_mono ?_ hclosed
          have h1 := bal_K' r (B - q + r - 1) 1
          rw [Nat.one_mul] at h1
          refine le_trans h1 (bal_mono (Nat.succ_pos r) ?_)
          omega
      rcases exists_extension hsym (le_refl q) hpq hcl_qR with ⟨z', hz'S, hpins'⟩
      let h0 : Finset (Fin n × G) := Q.image (fun u => (u, z' u))
      let ask' : StratW n G := fun rest => ask (h0 :: rest)
      have hwin' : ∃ ask' : StratW n G, ∀ x : Fin n → G, (∀ u ∈ S ∪ Q, x u = z' u) →
          (Finset.range r).sum (fun i => (batchW ask' x i).card) ≤ B - q ∧
          winW E ask' x (S ∪ Q) r := by
        refine ⟨ask', fun x hx => ?_⟩
        have hxS : ∀ u ∈ S, x u = z u := fun u hu =>
          (hx u (Finset.mem_union_left Q hu)).trans (hz'S u hu)
        have hh0 : h0 = (ask []).image (fun u => (u, x u)) := by
          dsimp only [h0, Q]
          refine Finset.image_congr ?_
          intro u hu
          dsimp only
          rw [hx u (Finset.mem_union_right S hu)]
        have hbatch_eq : ∀ i : Nat, batchW ask x (i + 1) = batchW ask' x i := by
          intro i
          unfold batchW
          rw [histW_shift ask x h0 hh0 i]
        rcases hask x hxS with ⟨hcard, hwin⟩
        constructor
        · rw [Finset.sum_range_succ'] at hcard
          have h00 : batchW ask x 0 = Q := rfl
          rw [h00] at hcard
          have hs : (Finset.range r).sum (fun i => (batchW ask x (i + 1)).card) =
              (Finset.range r).sum (fun i => (batchW ask' x i).card) :=
            Finset.sum_congr rfl (fun i _ => by rw [hbatch_eq i])
          rw [hs] at hcard
          omega
        · unfold winW at hwin ⊢
          dsimp only at hwin
          rw [seen_succ] at hwin
          have hseen_eq : (S ∪ batchW ask x 0) ∪ (Finset.range r).biUnion (fun i => batchW ask x (i + 1)) =
              (S ∪ Q) ∪ (Finset.range r).biUnion (batchW ask' x) := by
            congr 1
            refine Finset.biUnion_congr rfl ?_
            intro i _
            exact hbatch_eq i
          rw [hseen_eq] at hwin
          exact hwin
      rcases ih (B - q) (S ∪ Q) z' hwin' with hnp' | hnc'
      · exact hnp' hpins'
      · exact hnc' hcl_C

lemma fs_exists : ∀ r, 1 ≤ r → ∀ T, r ≤ T → ∃ fs : List Nat, fs.length = r ∧ (∀ f ∈ fs, 1 ≤ f) ∧
    fs.sum = T ∧ bal r T ≤ fs.prod := by
  intro r hr
  induction r, hr using Nat.le_induction with
  | base =>
      intro T hT
      refine ⟨[T], rfl, by simpa using hT, by simp, by simp [bal_one]⟩
  | succ r hr ih =>
      intro T hT
      set a := T / (r + 1) with ha
      have hapos : 1 ≤ a := Nat.div_pos hT (by omega)
      have hamul : a * (r + 1) ≤ T := Nat.div_mul_le_self T (r + 1)
      have har : r ≤ T - a := by
        have : r ≤ a * r := by nlinarith
        have : a * (r + 1) = a * r + a := by ring
        omega
      rcases ih (T - a) har with ⟨gs, hgl, hg1, hgs, hgp⟩
      refine ⟨a :: gs, by simp [hgl], ?_, ?_, ?_⟩
      · intro f hf
        rcases List.mem_cons.mp hf with h | h
        · omega
        · exact hg1 f h
      · simp only [List.sum_cons, hgs]
        have : a ≤ T := le_trans (Nat.le_mul_of_pos_right a (by omega)) hamul
        omega
      · rw [bal_peel (by omega) T, ← ha, List.prod_cons]
        exact Nat.mul_le_mul_left _ hgp

private lemma price_map (fs : List Nat) (h : ∀ f ∈ fs, 1 ≤ f) :
    (priceW (fs.map (· - 1))).1 = fs.prod := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
      have hf : 1 ≤ f := h f (by simp)
      have ih := ih (fun g hg => h g (by simp [hg]))
      dsimp only [priceW, List.foldr, List.map] at ih ⊢
      rw [ih, List.prod_cons, Nat.sub_add_cancel hf]

lemma sum_map_sub (fs : List Nat) (h : ∀ f ∈ fs, 1 ≤ f) :
    (fs.map (· - 1)).sum + fs.length = fs.sum := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
      have hf : 1 ≤ f := h f (by simp)
      have ih := ih (fun g hg => h g (by simp [hg]))
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      omega

private lemma budget_of_bs [DecidableEq G] (ask : StratW n G) (x : Fin n → G) (bs : List Nat)
    (h : ∀ i : Fin bs.length, (batchW ask x i.val).card ≤ bs[i.val]'i.isLt) :
    (Finset.range bs.length).sum (fun i => (batchW ask x i).card) ≤ bs.sum := by
  rw [Finset.sum_range]
  calc ∑ i : Fin bs.length, (batchW ask x i.val).card ≤ ∑ i : Fin bs.length, bs[i.val]'i.isLt :=
        Finset.sum_le_sum (fun i _ => h i)
    _ = bs.sum := by
        rw [← List.sum_ofFn]
        congr 1
        exact List.ofFn_getElem

end GroupWalks

end PEqualNP.Outside.L_pcx_309_aux

theorem PEqualNP.Outside.L_pcx_309 :
∀ (n : ℕ) (G : Type) [Group G] [DecidableEq G]
  (E : Fin n → Fin n → G → Prop),
  (∀ u v g, E u v g → E v u g⁻¹) →
  let walk := fun (m : ℕ) (v : ℕ → Fin n) (s : ℕ → G) =>
    ∀ i < m, E (v i) (v (i+1)) (s i)
  let gain := fun (m : ℕ) (s : ℕ → G) => ((List.range m).map s).prod
  let pinsOK := fun (S : Finset (Fin n)) (z : Fin n → G) (R : ℕ) =>
    ∀ m ≤ R, ∀ v s, walk m v s → v 0 ∈ S → v m ∈ S →
      z (v m) = z (v 0) * gain m s
  let closedOK := fun radius : ℕ =>
    ∀ m ≤ radius, ∀ v s, walk m v s → v 0 = v m → gain m s = 1
  let Strategy := List (Finset (Fin n × G)) → Finset (Fin n)
  let history := fun (ask : Strategy) (x : Fin n → G) (t : ℕ) =>
    (List.range t).foldl (fun hist _ => hist ++ [(ask hist).image (fun u => (u, x u))]) []
  let batch := fun (ask : Strategy) (x : Fin n → G) (i : ℕ) => ask (history ask x i)
  let win := fun (ask : Strategy) (x : Fin n → G) (S : Finset (Fin n)) (r : ℕ) =>
    let seen := S ∪ (Finset.range r).biUnion (batch ask x)
    ∃ u ∈ seen, ∃ v ∈ seen, ∃ g, E u v g ∧ x v ≠ x u * g
  let balanced := fun (r t : ℕ) => (t/r)^(r-(t % r)) * (t/r+1)^(t % r)
  ∀ (S : Finset (Fin n)) (z : Fin n → G) (r Q : ℕ), 0 < r →
  ((∃ ask : Strategy, ∀ x : Fin n → G, (∀ u ∈ S, x u = z u) →
      (Finset.range r).sum (fun round => (batch ask x round).card) ≤ Q ∧ win ask x S r) ↔ ¬ pinsOK S z (balanced r (Q+r)) ∨ ¬ closedOK (balanced r (Q+r-1))) := by
  intro n G _ _ E hsym walk gain pinsOK closedOK Strategy history batch win balanced S z r Q hr
  have hr0 : r ≠ 0 := Nat.pos_iff_ne_zero.mp hr
  constructor
  · intro h
    rcases PEqualNP.Outside.L_pcx_309_aux.adv309 E hsym r Q S z h with h1 | h2
    · exact Or.inl h1
    · rw [if_neg hr0] at h2
      exact Or.inr h2
  · rintro (hnp | hnc)
    · rcases PEqualNP.Outside.L_pcx_309_aux.fs_exists r hr (Q + r) (by omega) with ⟨fs, hfl, hf1, hfs, hfp⟩
      let bs := fs.map (· - 1)
      have hbl : bs.length = r := by simp [bs, hfl]
      have hbs : bs.sum = Q := by
        have := PEqualNP.Outside.L_pcx_309_aux.sum_map_sub fs hf1
        rw [hfl, hfs] at this
        simp only [bs]; omega
      have hnp' : ¬ PEqualNP.Outside.L_pcx_309_aux.pinsOKW E S z (PEqualNP.Outside.L_pcx_309_aux.priceW bs).1 := by
        intro hp
        apply hnp
        exact PEqualNP.Outside.L_pcx_309_aux.pinsOKW_mono (by rw [PEqualNP.Outside.L_pcx_309_aux.price_map fs hf1]; exact hfp) hp
      rcases (PEqualNP.Outside.L_pcx_309_aux.main_258 E hsym bs S z).mpr (Or.inl hnp') with ⟨ask, hask⟩
      refine ⟨ask, fun x hx => ?_⟩
      rcases hask x hx with ⟨hcard, hwin⟩
      have hb := PEqualNP.Outside.L_pcx_309_aux.budget_of_bs ask x bs hcard
      rw [hbl, hbs] at hb
      rw [hbl] at hwin
      exact ⟨hb, hwin⟩
    · by_cases hQ0 : Q = 0
      · exfalso
        apply hnc
        have h0 : PEqualNP.Outside.L_pcx_309_aux.bal r (Q + r - 1) = 0 := PEqualNP.Outside.L_pcx_309_aux.bal_small (by omega)
        intro m hm
        have hm' : m ≤ PEqualNP.Outside.L_pcx_309_aux.bal r (Q + r - 1) := hm
        rw [h0] at hm'
        exact PEqualNP.Outside.L_pcx_309_aux.closedOKW_zero E m hm'
      rcases PEqualNP.Outside.L_pcx_309_aux.fs_exists r hr (Q + r - 1) (by omega) with ⟨fs, hfl, hf1, hfs, hfp⟩
      cases fs with
      | nil => simp at hfl; omega
      | cons f0 gs =>
        let bs := f0 :: gs.map (· - 1)
        have hgl : gs.length = r - 1 := by simp at hfl; omega
        have hbl : bs.length = r := by simp [bs, hgl]; omega
        have hg1 : ∀ g ∈ gs, 1 ≤ g := fun g hg => hf1 g (by simp [hg])
        have hbs : bs.sum = Q := by
          have := PEqualNP.Outside.L_pcx_309_aux.sum_map_sub gs hg1
          simp only [List.sum_cons] at hfs
          simp only [bs, List.sum_cons]
          omega
        have hprice : (f0 :: gs).prod ≤ (PEqualNP.Outside.L_pcx_309_aux.priceW bs).2 := by
          have h2 : (PEqualNP.Outside.L_pcx_309_aux.priceW bs).2 = max (f0 * (PEqualNP.Outside.L_pcx_309_aux.priceW (gs.map (· - 1))).1) (PEqualNP.Outside.L_pcx_309_aux.priceW (gs.map (· - 1))).2 := rfl
          rw [h2, PEqualNP.Outside.L_pcx_309_aux.price_map gs hg1, List.prod_cons]
          exact le_max_left _ _
        have hnc' : ¬ PEqualNP.Outside.L_pcx_309_aux.closedOKW E (PEqualNP.Outside.L_pcx_309_aux.priceW bs).2 := by
          intro hc
          apply hnc
          exact PEqualNP.Outside.L_pcx_309_aux.closedOKW_mono (le_trans hfp hprice) hc
        rcases (PEqualNP.Outside.L_pcx_309_aux.main_258 E hsym bs S z).mpr (Or.inr hnc') with ⟨ask, hask⟩
        refine ⟨ask, fun x hx => ?_⟩
        rcases hask x hx with ⟨hcard, hwin⟩
        have hb := PEqualNP.Outside.L_pcx_309_aux.budget_of_bs ask x bs hcard
        rw [hbl, hbs] at hb
        rw [hbl] at hwin
        exact ⟨hb, hwin⟩
