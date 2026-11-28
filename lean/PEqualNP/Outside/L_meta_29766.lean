import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29766_aux

noncomputable section

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity.NestedCover
open Classical

abbrev F := ZMod 2

def b2z (b : Bool) : F := if b then 1 else 0

def chi (a : F) : ℤ := if a = 0 then 1 else -1

lemma zmod2_cases (a : F) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma zmod2_add_self (a : F) : a + a = 0 := by
  rcases zmod2_cases a with rfl | rfl <;> decide

lemma zmod2_mul_self (a : F) : a * a = a := by
  rcases zmod2_cases a with rfl | rfl <;> decide

lemma zmod2_eq_one_of_ne_zero {a : F} (h : a ≠ 0) : a = 1 := by
  rcases zmod2_cases a with rfl | rfl
  · exact absurd rfl h
  · rfl

lemma b2z_decide_eq_one (a : F) : b2z (decide (a = 1)) = a := by
  rcases zmod2_cases a with rfl | rfl <;> decide

lemma b2z_and (a b : Bool) : b2z (a && b) = b2z a * b2z b := by
  cases a <;> cases b <;> decide

lemma b2z_or (a b : Bool) : b2z (a || b) = b2z a + b2z b + b2z a * b2z b := by
  cases a <;> cases b <;> decide

lemma b2z_not (a : Bool) : b2z (!a) = b2z a + 1 := by
  cases a <;> decide

lemma b2z_mod2_pair (a b : Bool) :
    b2z (GateOp.eval (.mod 2) [a, b]) = b2z a + b2z b + 1 := by
  cases a <;> cases b <;> decide

lemma b2z_mod2_single (a : Bool) :
    b2z (GateOp.eval (.mod 2) [a]) = b2z a + 1 := by
  cases a <;> decide

lemma chi_add (a b : F) : chi (a + b) = chi a * chi b := by
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl <;> decide

lemma chi_natAbs (a : F) : (chi a).natAbs = 1 := by
  rcases zmod2_cases a with rfl | rfl <;> decide

lemma raw_term_eq_chi (c : Bool) (t : F) :
    (if c = decide (t = 1) then (1 : ℤ) else -1) = chi (b2z c + t) := by
  cases c <;> rcases zmod2_cases t with rfl | rfl <;> decide

lemma sum_zmod2 {α : Type*} [AddCommMonoid α] (f : F → α) : ∑ u : F, f u = f 0 + f 1 := by
  rw [Fintype.sum_eq_add (0 : F) (1 : F) (by decide)
    (fun u ⟨h0, h1⟩ => by rcases zmod2_cases u with rfl | rfl; exact absurd rfl h0; exact absurd rfl h1)]

lemma sum_zmod2_shift (α : F) (f : F → ℤ) : ∑ u : F, f u = f α + f (α + 1) := by
  rw [sum_zmod2]
  rcases zmod2_cases α with rfl | rfl
  · simp
  · simp [show (1 : F) + 1 = 0 by decide, add_comm]

lemma sum_chi_zmod2 (a : F) : ∑ u : F, chi (a * u) = if a = 0 then 2 else 0 := by
  rcases zmod2_cases a with rfl | rfl <;> decide

lemma sum_chi_dot_fin : ∀ (l : ℕ) (v : Fin l → F),
    ∑ c : Fin l → F, chi (∑ r : Fin l, c r * v r) =
      if ∀ r : Fin l, v r = 0 then (2 : ℤ) ^ l else 0 := by
  intro l
  induction l with
  | zero =>
    intro v
    have h0 : ∀ r : Fin 0, v r = 0 := fun r => Fin.elim0 r
    simp [h0, chi]
  | succ l ih =>
    intro v
    let e := (Fin.consEquiv (fun _ : Fin (l + 1) => F))
    rw [← Fintype.sum_equiv e _ _ (fun _ => rfl), Fintype.sum_prod_type]
    have hterm : ∀ (u : F) (c : Fin l → F),
        chi (∑ r : Fin (l + 1), e (u, c) r * v r) =
        chi (v 0 * u) * chi (∑ r : Fin l, c r * v r.succ) := by
      intro u c
      rw [Fin.sum_univ_succ, chi_add]
      congr 1
      dsimp [e]; simp [mul_comm]
    simp_rw [hterm, ← Finset.mul_sum, ← Finset.sum_mul, sum_chi_zmod2, ih]
    by_cases hv : ∀ r : Fin (l + 1), v r = 0
    · simp [hv, pow_succ']
    · simp only [hv, ↓reduceIte]
      by_cases h0 : v 0 = 0
      · have hs : ¬ ∀ r : Fin l, v r.succ = 0 := by
          intro h; exact hv (fun r => Fin.cases h0 h r)
        simp only [h0, hs, ↓reduceIte, mul_zero]
      · simp only [h0, ↓reduceIte, zero_mul]

lemma sum_chi_two_vars (lb lc : F) :
    ∑ u : F, ∑ v : F, chi (u * v + u * lb + v * lc) = 2 * chi (lb * lc) := by
  rcases zmod2_cases lb with rfl | rfl <;> rcases zmod2_cases lc with rfl | rfl <;> decide

lemma sum_chi_cubic_triple :
    ∑ u : F, ∑ v : F, ∑ w : F, chi (u * v * w) = 6 := by
  decide

lemma natAbs_sum_le {α : Type*} (s : Finset α) (f : α → ℤ) :
    (∑ a ∈ s, f a).natAbs ≤ ∑ a ∈ s, (f a).natAbs := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact le_trans (Int.natAbs_add_le _ _) (Nat.add_le_add_left ih _)

lemma natAbs_sum_chi_le {α : Type*} (s : Finset α) (f : α → F) :
    (∑ a ∈ s, chi (f a)).natAbs ≤ s.card := by
  calc (∑ a ∈ s, chi (f a)).natAbs
      ≤ ∑ a ∈ s, (chi (f a)).natAbs := natAbs_sum_le s (fun a => chi (f a))
    _ = ∑ _a ∈ s, 1 := Finset.sum_congr rfl (fun a _ => chi_natAbs (f a))
    _ = s.card := by simp

lemma pow_three_four_mono {a b : ℕ} (h : a ≤ b) (X Y : ℕ)
    (hY : 4 ^ b * X ≤ Y * 3 ^ b) : 4 ^ a * X ≤ Y * 3 ^ a := by
  have hpow : 3 ^ (b - a) ≤ 4 ^ (b - a) := Nat.pow_le_pow_left (by omega) _
  have h1 : 4 ^ a * 3 ^ (b - a) * X ≤ 4 ^ b * X := by
    have hsplit : 4 ^ b = 4 ^ a * 4 ^ (b - a) := by rw [← pow_add, Nat.add_sub_of_le h]
    rw [hsplit]
    calc 4 ^ a * 3 ^ (b - a) * X
        = (4 ^ a * X) * 3 ^ (b - a) := by ring
      _ ≤ (4 ^ a * X) * 4 ^ (b - a) := Nat.mul_le_mul_left _ hpow
      _ = 4 ^ a * 4 ^ (b - a) * X := by ring
  have h2 : 4 ^ a * 3 ^ (b - a) * X ≤ Y * 3 ^ a * 3 ^ (b - a) := by
    have hsplit : 3 ^ b = 3 ^ a * 3 ^ (b - a) := by rw [← pow_add, Nat.add_sub_of_le h]
    rw [hsplit] at hY
    calc 4 ^ a * 3 ^ (b - a) * X ≤ 4 ^ b * X := h1
      _ ≤ Y * (3 ^ a * 3 ^ (b - a)) := hY
      _ = Y * 3 ^ a * 3 ^ (b - a) := by ring
  have hpos : 0 < 3 ^ (b - a) := Nat.pow_pos (by omega)
  have h3 : (4 ^ a * X) * 3 ^ (b - a) ≤ (Y * 3 ^ a) * 3 ^ (b - a) := by
    calc (4 ^ a * X) * 3 ^ (b - a) = 4 ^ a * 3 ^ (b - a) * X := by ring
      _ ≤ Y * 3 ^ a * 3 ^ (b - a) := h2
  exact Nat.le_of_mul_le_mul_right h3 hpos

lemma leaf_rate_mono {b l j j' X Y : ℕ} (hbl : b ≤ l) (hjj : j ≤ j' + 2 * (l - b))
    (hbound : 4 ^ j' * X ≤ Y * 3 ^ j') :
    2 ^ b * 4 ^ j * X ≤ 2 ^ l * Y * 3 ^ j := by
  let d := l - b
  have hl : l = b + d := (Nat.add_sub_of_le hbl).symm
  have hstep : ∀ t r : ℕ, 4 ^ (r + 2 * t) * 3 ^ r ≤ 2 ^ t * 4 ^ r * 3 ^ (r + 2 * t) := by
    intro t r
    induction t with
    | zero => simp
    | succ t ih =>
      have h1 : 4 ^ (r + 2 * (t + 1)) = 4 ^ (r + 2 * t) * 16 := by
        rw [show r + 2 * (t + 1) = (r + 2 * t) + 2 by omega, pow_add]; norm_num
      have h2 : 3 ^ (r + 2 * (t + 1)) = 3 ^ (r + 2 * t) * 9 := by
        rw [show r + 2 * (t + 1) = (r + 2 * t) + 2 by omega, pow_add]; norm_num
      have h3 : 2 ^ (t + 1) = 2 ^ t * 2 := by rw [pow_succ]
      rw [h1, h2, h3]
      have h16 : 16 ≤ 2 * 9 := by omega
      calc 4 ^ (r + 2 * t) * 16 * 3 ^ r
          = (4 ^ (r + 2 * t) * 3 ^ r) * 16 := by ring
        _ ≤ (2 ^ t * 4 ^ r * 3 ^ (r + 2 * t)) * (2 * 9) := Nat.mul_le_mul ih h16
        _ = 2 ^ t * 2 * 4 ^ r * (3 ^ (r + 2 * t) * 9) := by ring
  have hmain : 4 ^ (j' + 2 * d) * X ≤ 2 ^ d * Y * 3 ^ (j' + 2 * d) := by
    have hmul : 4 ^ (j' + 2 * d) * (X * 3 ^ j') ≤ (2 ^ d * Y * 3 ^ (j' + 2 * d)) * 3 ^ j' := by
      calc 4 ^ (j' + 2 * d) * (X * 3 ^ j')
          = (4 ^ (j' + 2 * d) * 3 ^ j') * X := by ring
        _ ≤ (2 ^ d * 4 ^ j' * 3 ^ (j' + 2 * d)) * X := Nat.mul_le_mul_right X (hstep d j')
        _ = 2 ^ d * 3 ^ (j' + 2 * d) * (4 ^ j' * X) := by ring
        _ ≤ 2 ^ d * 3 ^ (j' + 2 * d) * (Y * 3 ^ j') := Nat.mul_le_mul_left _ hbound
        _ = (2 ^ d * Y * 3 ^ (j' + 2 * d)) * 3 ^ j' := by ring
    have hpos : 0 < 3 ^ j' := Nat.pow_pos (by omega)
    have hmul' : (4 ^ (j' + 2 * d) * X) * 3 ^ j' ≤ (2 ^ d * Y * 3 ^ (j' + 2 * d)) * 3 ^ j' := by
      calc (4 ^ (j' + 2 * d) * X) * 3 ^ j' = 4 ^ (j' + 2 * d) * (X * 3 ^ j') := by ring
        _ ≤ (2 ^ d * Y * 3 ^ (j' + 2 * d)) * 3 ^ j' := hmul
    exact Nat.le_of_mul_le_mul_right hmul' hpos
  have hjbound : 4 ^ j * X ≤ (2 ^ d * Y) * 3 ^ j := pow_three_four_mono hjj X (2 ^ d * Y) hmain
  rw [hl, pow_add]
  calc 2 ^ b * 4 ^ j * X = 2 ^ b * (4 ^ j * X) := by ring
    _ ≤ 2 ^ b * (2 ^ d * Y * 3 ^ j) := Nat.mul_le_mul_left _ hjbound
    _ = 2 ^ b * 2 ^ d * Y * 3 ^ j := by ring

lemma sum_over_partition {α γ β : Type*} [DecidableEq γ] [AddCommMonoid β]
    (ls : List α) (S : Finset γ) (P : α → γ → Prop) [∀ a x, Decidable (P a x)]
    (hpart : ∀ x ∈ S, ∃! idx : Fin ls.length, P (ls.get idx) x)
    (hsub : ∀ idx : Fin ls.length, ∀ x, P (ls.get idx) x → x ∈ S)
    (f : γ → β) :
    ∑ x ∈ S, f x = ∑ idx : Fin ls.length, ∑ x ∈ S.filter (fun x => P (ls.get idx) x), f x := by
  let gOpt : γ → Option (Fin ls.length) := fun x =>
    if hx : x ∈ S then some (Classical.choose (hpart x hx)) else none
  have hg_spec : ∀ x (hx : x ∈ S), P (ls.get (Classical.choose (hpart x hx))) x :=
    fun x hx => (Classical.choose_spec (hpart x hx)).1
  have hg_uniq : ∀ x (hx : x ∈ S) (idx : Fin ls.length), P (ls.get idx) x →
      idx = Classical.choose (hpart x hx) :=
    fun x hx idx hP => (Classical.choose_spec (hpart x hx)).2 idx hP
  have hfib : ∑ idx : Fin ls.length, ∑ x ∈ S.filter (fun x => P (ls.get idx) x), f x =
      ∑ idx : Fin ls.length, ∑ x ∈ S.filter (fun x => gOpt x = some idx), f x := by
    apply Finset.sum_congr rfl; intro idx _
    congr 1; ext x
    simp only [Finset.mem_filter, gOpt]
    constructor
    · rintro ⟨hx, hP⟩
      refine ⟨hx, ?_⟩
      simp only [hx, ↓reduceDIte]
      exact congrArg some (hg_uniq x hx idx hP).symm
    · rintro ⟨hx, hEq⟩
      simp only [hx, ↓reduceDIte] at hEq
      have hidx : Classical.choose (hpart x hx) = idx := Option.some.inj hEq
      exact ⟨hx, hidx ▸ hg_spec x hx⟩
  rw [hfib]
  have h1 := Finset.sum_fiberwise_of_maps_to (s := S) (t := (Finset.univ : Finset (Fin ls.length)).image some)
    (g := gOpt) (f := f) (fun x hx => by
      dsimp [gOpt]; simp only [hx, ↓reduceDIte]
      exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩)
  rw [Finset.sum_image (fun a _ b _ h => Option.some.inj h)] at h1
  exact h1.symm

lemma list_flatMap_partition {α β γ : Type*}
    (ls : List α) (f : α → List β) (P : α → γ → Prop) (Q : β → γ → Prop)
    (hpart : ∀ x : γ, ∃! i : Fin ls.length, P (ls.get i) x)
    (hchild : ∀ a ∈ ls, ∀ x : γ, P a x → ∃! j : Fin (f a).length, Q ((f a).get j) x)
    (hsub : ∀ a ∈ ls, ∀ b ∈ f a, ∀ x : γ, Q b x → P a x) :
    ∀ x : γ, ∃! idx : Fin (ls.flatMap f).length, Q ((ls.flatMap f).get idx) x := by
  intro x
  have haux : ∀ (ls' : List α),
      (∀ a ∈ ls', ∀ b ∈ f a, Q b x → P a x) →
      (∀ a ∈ ls', P a x → ∃! j : Fin (f a).length, Q ((f a).get j) x) →
      (∀ i1 i2 : Fin ls'.length, P (ls'.get i1) x → P (ls'.get i2) x → i1 = i2) →
      (∃ i : Fin ls'.length, P (ls'.get i) x) →
      ∃! idx : Fin (ls'.flatMap f).length, Q ((ls'.flatMap f).get idx) x := by
    intro ls'
    induction ls' with
    | nil => rintro _ _ _ ⟨i, _⟩; exact Fin.elim0 i
    | cons a rest ih =>
      intro hsub' hch' huniq' ⟨i, hi⟩
      have hlen_cons : ((a :: rest).flatMap f).length = (f a).length + (rest.flatMap f).length := by
        rw [List.flatMap_cons, List.length_append]
      by_cases ha : P a x
      · obtain ⟨j, hjQ, hjU⟩ := hch' a (List.mem_cons_self ..) ha
        have hnone_rest : ∀ i' : Fin rest.length, ¬ P (rest.get i') x := by
          intro i' hP'
          have h0 := huniq' ⟨0, by simp⟩ i'.succ ha hP'
          exact Fin.succ_ne_zero i' h0.symm
        have hnone_flat : ∀ k : Fin (rest.flatMap f).length, ¬ Q ((rest.flatMap f).get k) x := by
          intro k hQk
          have hmem : (rest.flatMap f).get k ∈ rest.flatMap f := List.get_mem _ _
          obtain ⟨a', ha', hba'⟩ := List.mem_flatMap.mp hmem
          obtain ⟨i', hi'⟩ := List.mem_iff_get.mp ha'
          have hPa' : P a' x := hsub' a' (List.mem_cons_of_mem a ha') _ hba' hQk
          rw [← hi'] at hPa'
          exact hnone_rest i' hPa'
        refine ⟨⟨j.val, by have := j.isLt; omega⟩, ?_, ?_⟩
        · simp only [List.flatMap_cons, List.get_eq_getElem, List.getElem_append_left j.isLt]
          exact hjQ
        · intro idx2 hQ2
          by_cases hlt : idx2.val < (f a).length
          · simp only [List.flatMap_cons, List.get_eq_getElem, List.getElem_append_left hlt] at hQ2
            have heq := hjU ⟨idx2.val, hlt⟩ hQ2
            exact Fin.ext (show idx2.val = j.val from congrArg Fin.val heq)
          · have hge : (f a).length ≤ idx2.val := by omega
            have hlt2 : idx2.val - (f a).length < (rest.flatMap f).length := by
              have := idx2.isLt; omega
            simp only [List.flatMap_cons, List.get_eq_getElem, List.getElem_append_right hge] at hQ2
            exact absurd hQ2 (hnone_flat ⟨idx2.val - (f a).length, hlt2⟩)
      · have hex_rest : ∃ i' : Fin rest.length, P (rest.get i') x := by
          refine Fin.cases (fun h => absurd h ha) (fun i' h => ⟨i', h⟩) i hi
        have huniq_rest : ∀ i1 i2 : Fin rest.length, P (rest.get i1) x → P (rest.get i2) x → i1 = i2 := by
          intro i1 i2 h1 h2
          exact Fin.succ_injective _ (huniq' i1.succ i2.succ h1 h2)
        obtain ⟨k, hkQ, hkU⟩ := ih
          (fun a' ha' => hsub' a' (List.mem_cons_of_mem a ha'))
          (fun a' ha' => hch' a' (List.mem_cons_of_mem a ha'))
          huniq_rest hex_rest
        refine ⟨⟨(f a).length + k.val, by have := k.isLt; omega⟩, ?_, ?_⟩
        · simp only [List.flatMap_cons, List.get_eq_getElem,
            List.getElem_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
          exact hkQ
        · intro idx2 hQ2
          by_cases hlt : idx2.val < (f a).length
          · simp only [List.flatMap_cons, List.get_eq_getElem, List.getElem_append_left hlt] at hQ2
            have hmem : (f a)[idx2.val]'hlt ∈ f a := List.getElem_mem hlt
            exact absurd (hsub' a (List.mem_cons_self ..) _ hmem hQ2) ha
          · have hge : (f a).length ≤ idx2.val := by omega
            have hlt2 : idx2.val - (f a).length < (rest.flatMap f).length := by
              have := idx2.isLt; omega
            simp only [List.flatMap_cons, List.get_eq_getElem, List.getElem_append_right hge] at hQ2
            have heq := hkU ⟨idx2.val - (f a).length, hlt2⟩ hQ2
            have hval : idx2.val - (f a).length = k.val := congrArg Fin.val heq
            exact Fin.ext (by dsimp; omega)
  obtain ⟨i0, hi0, huniq0⟩ := hpart x
  exact haux ls (fun a ha b hb => hsub a ha b hb x) (fun a ha => hchild a ha x)
    (fun i1 i2 h1 h2 => by rw [huniq0 i1 h1, huniq0 i2 h2]) ⟨i0, hi0⟩

def IsAffine {ι : Type} [Fintype ι] (L : (ι → F) → F) : Prop :=
  ∃ (v : ι → F) (c : F), ∀ y, L y = (∑ i, v i * y i) + c

def IsQuad {ι : Type} [Fintype ι] (Q : (ι → F) → F) : Prop :=
  ∃ (M : ι → ι → F) (c : F), ∀ y, Q y = (∑ i, ∑ j, M i j * y i * y j) + c

lemma isQuad_add {ι : Type} [Fintype ι] {Q1 Q2 : (ι → F) → F}
    (h1 : IsQuad Q1) (h2 : IsQuad Q2) : IsQuad (fun y => Q1 y + Q2 y) := by
  obtain ⟨M1, c1, hM1⟩ := h1
  obtain ⟨M2, c2, hM2⟩ := h2
  refine ⟨fun i j => M1 i j + M2 i j, c1 + c2, fun y => ?_⟩
  dsimp only
  rw [hM1 y, hM2 y]
  have hsum : ∑ i, ∑ j, (M1 i j + M2 i j) * y i * y j =
      (∑ i, ∑ j, M1 i j * y i * y j) + (∑ i, ∑ j, M2 i j * y i * y j) := by
    simp only [add_mul, Finset.sum_add_distrib]
  rw [hsum]; ring

lemma isQuad_of_isAffine {ι : Type} [Fintype ι] [DecidableEq ι] {L : (ι → F) → F}
    (hL : IsAffine L) : IsQuad L := by
  obtain ⟨v, c, hv⟩ := hL
  refine ⟨fun i j => if i = j then v i else 0, c, fun y => ?_⟩
  rw [hv y]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have : ∑ j, (if i = j then v i else 0) * y i * y j = v i * y i * y i := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji; simp [Ne.symm hji]
    · intro h; exact absurd (Finset.mem_univ i) h
  rw [this, mul_assoc, zmod2_mul_self]

lemma isQuad_mul_affine {ι : Type} [Fintype ι] [DecidableEq ι] {L1 L2 : (ι → F) → F}
    (h1 : IsAffine L1) (h2 : IsAffine L2) : IsQuad (fun y => L1 y * L2 y) := by
  obtain ⟨v1, c1, hv1⟩ := h1
  obtain ⟨v2, c2, hv2⟩ := h2
  have hq0 : IsQuad (fun y => (∑ i, v1 i * y i) * (∑ j, v2 j * y j)) := by
    refine ⟨fun i j => v1 i * v2 j, 0, fun y => ?_⟩
    dsimp only
    rw [add_zero, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _; ring
  have hq1 : IsQuad (fun y => c2 * (∑ i, v1 i * y i) + c1 * (∑ j, v2 j * y j) + c1 * c2) := by
    apply isQuad_of_isAffine
    refine ⟨fun i => c2 * v1 i + c1 * v2 i, c1 * c2, fun y => ?_⟩
    dsimp only
    simp only [add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
  obtain ⟨M, c, hM⟩ := isQuad_add hq0 hq1
  refine ⟨M, c, fun y => ?_⟩
  dsimp only
  have heq : L1 y * L2 y = (∑ i, v1 i * y i) * (∑ j, v2 j * y j) +
      (c2 * (∑ i, v1 i * y i) + c1 * (∑ j, v2 j * y j) + c1 * c2) := by
    rw [hv1 y, hv2 y]; ring
  rw [heq]; exact hM y

lemma isQuad_sum {α ι : Type} [Fintype ι] (s : Finset α) (f : α → (ι → F) → F)
    (hf : ∀ a ∈ s, IsQuad (f a)) : IsQuad (fun y => ∑ a ∈ s, f a y) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨fun _ _ => 0, 0, fun _ => by simp⟩
  | insert a s ha ih =>
    obtain ⟨M, c, hM⟩ := isQuad_add (hf a (Finset.mem_insert_self a s))
      (ih (fun b hb => hf b (Finset.mem_insert_of_mem hb)))
    refine ⟨M, c, fun y => ?_⟩
    dsimp only
    rw [Finset.sum_insert ha]
    exact hM y

lemma isQuad_comp_affine {ι ι' : Type} [Fintype ι] [Fintype ι'] [DecidableEq ι']
    {Q : (ι → F) → F} (hQ : IsQuad Q) {φ : (ι' → F) → (ι → F)}
    (hφ : ∀ i, IsAffine (fun z => φ z i)) : IsQuad (fun z => Q (φ z)) := by
  obtain ⟨M, c, hM⟩ := hQ
  have hterm : ∀ i j : ι, IsQuad (fun z => M i j * φ z i * φ z j) := by
    intro i j
    have h1 : IsAffine (fun z => M i j * φ z i) := by
      obtain ⟨v, c0, hv⟩ := hφ i
      refine ⟨fun x => M i j * v x, M i j * c0, fun z => ?_⟩
      dsimp only
      have hvi := hv z
      dsimp only at hvi
      rw [hvi, mul_add, Finset.mul_sum]
      congr 1; apply Finset.sum_congr rfl; intro x _; ring
    exact isQuad_mul_affine h1 (hφ j)
  have hdouble : IsQuad (fun z => ∑ i : ι, ∑ j : ι, M i j * φ z i * φ z j) :=
    isQuad_sum Finset.univ _ (fun i _ => isQuad_sum Finset.univ _ (fun j _ => hterm i j))
  have hc_quad : IsQuad (fun _ : ι' → F => c) := ⟨fun _ _ => 0, c, fun _ => by simp⟩
  obtain ⟨M0, c0, hM0⟩ := isQuad_add hdouble hc_quad
  refine ⟨M0, c0, fun z => ?_⟩
  dsimp only
  rw [hM (φ z)]
  exact hM0 z

theorem cubic_bound_unconstrained :
    ∀ (m : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι] (pos : Fin m × Fin 3 ↪ ι)
      (Q : (ι → F) → F), IsQuad Q →
      4 ^ m * (∑ y : ι → F, chi (Q y + ∑ i : Fin m, y (pos (i, 0)) * y (pos (i, 1)) * y (pos (i, 2)))).natAbs
        ≤ Fintype.card (ι → F) * 3 ^ m := by
  intro m
  induction m with
  | zero =>
    intro ι _ _ _ Q _
    simp only [pow_zero, one_mul, mul_one, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
    exact natAbs_sum_chi_le Finset.univ Q
  | succ m ih =>
    intro ι _ _ pos Q hQ
    let a : ι := pos (Fin.last m, 0)
    let b : ι := pos (Fin.last m, 1)
    let c : ι := pos (Fin.last m, 2)
    have hab : a ≠ b := fun h => by have := pos.injective h; simp at this
    have hac : a ≠ c := fun h => by have := pos.injective h; simp at this
    have hbc : b ≠ c := fun h => by have := pos.injective h; simp at this
    let ι' := {x : ι // x ≠ a ∧ x ≠ b ∧ x ≠ c}
    let embed : (F × F × F) × (ι' → F) → (ι → F) := fun p x =>
      if h1 : x = a then p.1.1
      else if h2 : x = b then p.1.2.1
      else if h3 : x = c then p.1.2.2
      else p.2 ⟨x, h1, h2, h3⟩
    let split : (ι → F) → (F × F × F) × (ι' → F) := fun y =>
      ((y a, y b, y c), fun x => y x.1)
    let hEquiv : (ι → F) ≃ (F × F × F) × (ι' → F) :=
      { toFun := split
        invFun := embed
        left_inv := fun y => by
          funext x
          dsimp [embed, split]
          split_ifs with h1 h2 h3
          · subst h1; rfl
          · subst h2; rfl
          · subst h3; rfl
          · rfl
        right_inv := fun ⟨⟨ua, ub, uc⟩, yr⟩ => by
          apply Prod.ext
          · apply Prod.ext
            · simp [embed, split]
            · apply Prod.ext
              · simp [embed, split, Ne.symm hab]
              · simp [embed, split, Ne.symm hac, Ne.symm hbc]
          · funext x
            simp [embed, split, x.2.1, x.2.2.1, x.2.2.2] }
    have hcard : Fintype.card (ι → F) = 8 * Fintype.card (ι' → F) := by
      rw [Fintype.card_congr hEquiv, Fintype.card_prod, Fintype.card_prod, Fintype.card_prod, ZMod.card 2]
    let pos' : Fin m × Fin 3 ↪ ι' :=
      ⟨fun p => ⟨pos (p.1.castSucc, p.2), by
        refine ⟨?_, ?_, ?_⟩ <;> intro h <;> have h' := pos.injective h
        · exact Fin.castSucc_ne_last p.1 (Prod.mk.inj h').1
        · exact Fin.castSucc_ne_last p.1 (Prod.mk.inj h').1
        · exact Fin.castSucc_ne_last p.1 (Prod.mk.inj h').1⟩,
       fun p1 p2 h => by
        have h1 : pos (p1.1.castSucc, p1.2) = pos (p2.1.castSucc, p2.2) := congrArg Subtype.val h
        have h2 := pos.injective h1
        exact Prod.ext (Fin.castSucc_injective m (Prod.mk.inj h2).1) (Prod.mk.inj h2).2⟩
    let gRest : (ι' → F) → F := fun yr =>
      ∑ i : Fin m, yr (pos' (i, 0)) * yr (pos' (i, 1)) * yr (pos' (i, 2))
    have hg_embed : ∀ ua ub uc yr,
        (∑ i : Fin (m + 1), embed ((ua, ub, uc), yr) (pos (i, 0)) *
          embed ((ua, ub, uc), yr) (pos (i, 1)) * embed ((ua, ub, uc), yr) (pos (i, 2))) =
        gRest yr + ua * ub * uc := by
      intro ua ub uc yr
      rw [Fin.sum_univ_castSucc]
      congr 1
      · apply Finset.sum_congr rfl
        intro i _
        have hval : ∀ t : Fin 3, embed ((ua, ub, uc), yr) (pos (i.castSucc, t)) = yr (pos' (i, t)) := by
          intro t
          have hp := (pos' (i, t)).2
          have hp1 : pos (i.castSucc, t) ≠ a := hp.1
          have hp2 : pos (i.castSucc, t) ≠ b := hp.2.1
          have hp3 : pos (i.castSucc, t) ≠ c := hp.2.2
          dsimp [embed, pos']
          simp only [hp1, hp2, hp3, ↓reduceDIte]
          rfl
        rw [hval 0, hval 1, hval 2]
      · have h0 : embed ((ua, ub, uc), yr) a = ua := by simp [embed]
        have h1 : embed ((ua, ub, uc), yr) b = ub := by simp [embed, Ne.symm hab]
        have h2 : embed ((ua, ub, uc), yr) c = uc := by simp [embed, Ne.symm hac, Ne.symm hbc]
        exact congrArg₂ (· * ·) (congrArg₂ (· * ·) h0 h1) h2
    obtain ⟨M, c0, hM⟩ := hQ
    let α : F := M b c + M c b
    let Lb : F → (ι' → F) → F := fun ua yr =>
      M b b + (M b a + M a b) * ua + ∑ x : ι', (M b x.1 + M x.1 b) * yr x
    let Lc : F → (ι' → F) → F := fun ua yr =>
      M c c + (M c a + M a c) * ua + ∑ x : ι', (M c x.1 + M x.1 c) * yr x
    let R : F → (ι' → F) → F := fun ua yr =>
      Q (embed ((ua, 0, 0), yr))
    have hLb_aff : ∀ ua, IsAffine (Lb ua) := fun ua =>
      ⟨fun x => M b x.1 + M x.1 b, M b b + (M b a + M a b) * ua, fun yr => by dsimp [Lb]; ring⟩
    have hLc_aff : ∀ ua, IsAffine (Lc ua) := fun ua =>
      ⟨fun x => M c x.1 + M x.1 c, M c c + (M c a + M a c) * ua, fun yr => by dsimp [Lc]; ring⟩
    have hR_quad : ∀ ua, IsQuad (R ua) := by
      intro ua
      apply isQuad_comp_affine ⟨M, c0, hM⟩
      intro i
      dsimp [embed]
      split_ifs with h1 h2 h3
      · exact ⟨fun _ => 0, ua, fun _ => by simp⟩
      · exact ⟨fun _ => 0, 0, fun _ => by simp⟩
      · exact ⟨fun _ => 0, 0, fun _ => by simp⟩
      · exact ⟨fun x => if x = ⟨i, h1, h2, h3⟩ then 1 else 0, 0, fun yr => by simp⟩
    have hQ_decomp : ∀ ua ub uc yr,
        Q (embed ((ua, ub, uc), yr)) = α * ub * uc + ub * Lb ua yr + uc * Lc ua yr + R ua yr := by
      intro ua ub uc yr
      have hterm : ∀ f : ι → F,
          ∑ i : ι, f i = f a + f b + f c + ∑ x : ι', f x.1 := by
        intro f
        let S : Finset ι := {a, b, c}
        have hcomp : ∑ i : ι, f i = (∑ i ∈ S, f i) + ∑ i ∈ Finset.univ \ S, f i :=
          (Finset.sum_add_sum_compl S f).symm
        rw [hcomp]
        have hS : ∑ i ∈ S, f i = f a + f b + f c := by
          dsimp [S]
          rw [Finset.sum_insert (by simp [hab, hac]), Finset.sum_insert (by simp [hbc]),
            Finset.sum_singleton, add_assoc]
        rw [hS]
        congr 1
        symm
        refine Finset.sum_bij (fun (x : ι') _ => x.1) ?_ ?_ ?_ ?_
        · intro x _; simp [S, x.2.1, x.2.2.1, x.2.2.2]
        · intro x1 _ x2 _ h; exact Subtype.ext h
        · intro i hi
          simp only [S, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert,
            Finset.mem_singleton, true_and, not_or] at hi
          exact ⟨⟨i, hi.1, hi.2.1, hi.2.2⟩, Finset.mem_univ _, rfl⟩
        · intro _ _; rfl
      have hval : ∀ y : ι → F,
          Q y = (M b c + M c b) * y b * y c +
            y b * (M b b + (M b a + M a b) * y a + ∑ x : ι', (M b x.1 + M x.1 b) * y x.1) +
            y c * (M c c + (M c a + M a c) * y a + ∑ x : ι', (M c x.1 + M x.1 c) * y x.1) +
            (M a a * y a * y a + ∑ x : ι', (M a x.1 + M x.1 a) * y a * y x.1 +
              ∑ x : ι', ∑ z : ι', M x.1 z.1 * y x.1 * y z.1 + c0) := by
        intro y
        rw [hM y, hterm]
        simp_rw [hterm]
        have hbb : M b b * y b * y b = y b * M b b := by
          rw [mul_assoc, zmod2_mul_self, mul_comm]
        have hcc : M c c * y c * y c = y c * M c c := by
          rw [mul_assoc, zmod2_mul_self, mul_comm]
        have hsum_b : y b * ∑ x : ι', (M b x.1 + M x.1 b) * y x.1 =
            (∑ x : ι', M b x.1 * y b * y x.1) + (∑ x : ι', M x.1 b * y x.1 * y b) := by
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro x _; ring
        have hsum_c : y c * ∑ x : ι', (M c x.1 + M x.1 c) * y x.1 =
            (∑ x : ι', M c x.1 * y c * y x.1) + (∑ x : ι', M x.1 c * y x.1 * y c) := by
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro x _; ring
        have hsum_a : ∑ x : ι', (M a x.1 + M x.1 a) * y a * y x.1 =
            (∑ x : ι', M a x.1 * y a * y x.1) + (∑ x : ι', M x.1 a * y x.1 * y a) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro x _; ring
        simp only [Finset.sum_add_distrib]
        rw [hbb, hcc]
        have hrhs : y b * (M b b + (M b a + M a b) * y a + ∑ x : ι', (M b x.1 + M x.1 b) * y x.1) =
            y b * M b b + y b * ((M b a + M a b) * y a) +
              ((∑ x : ι', M b x.1 * y b * y x.1) + (∑ x : ι', M x.1 b * y x.1 * y b)) := by
          rw [mul_add, mul_add, hsum_b]
        have hrhs2 : y c * (M c c + (M c a + M a c) * y a + ∑ x : ι', (M c x.1 + M x.1 c) * y x.1) =
            y c * M c c + y c * ((M c a + M a c) * y a) +
              ((∑ x : ι', M c x.1 * y c * y x.1) + (∑ x : ι', M x.1 c * y x.1 * y c)) := by
          rw [mul_add, mul_add, hsum_c]
        rw [hrhs, hrhs2, hsum_a]
        ring
      have hv1 := hval (embed ((ua, ub, uc), yr))
      have hv0 := hval (embed ((ua, 0, 0), yr))
      have he_a : ∀ u1 u2, embed ((ua, u1, u2), yr) a = ua := fun _ _ => by simp [embed]
      have he_b : ∀ u1 u2, embed ((ua, u1, u2), yr) b = u1 := fun _ _ => by simp [embed, Ne.symm hab]
      have he_c : ∀ u1 u2, embed ((ua, u1, u2), yr) c = u2 := fun _ _ => by simp [embed, Ne.symm hac, Ne.symm hbc]
      have he_x : ∀ u1 u2 (x : ι'), embed ((ua, u1, u2), yr) x.1 = yr x := fun _ _ x => by
        simp [embed, x.2.1, x.2.2.1, x.2.2.2]
      simp only [he_a, he_b, he_c, he_x] at hv1 hv0
      dsimp [R, α, Lb, Lc]
      rw [hv1, hv0]
      ring

    let Sfull : ℤ := ∑ y : ι → F, chi (Q y + ∑ i : Fin (m + 1), y (pos (i, 0)) * y (pos (i, 1)) * y (pos (i, 2)))
    let Sbranch (ua : F) : ℤ :=
      ∑ ub : F, ∑ uc : F, ∑ yr : ι' → F,
        chi ((α + ua) * ub * uc + ub * Lb ua yr + uc * Lc ua yr + R ua yr + gRest yr)
    have hS_split : Sfull = Sbranch α + Sbranch (α + 1) := by
      dsimp [Sfull]
      rw [← Fintype.sum_equiv hEquiv.symm _ _ (fun _ => rfl)]
      rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
      rw [sum_zmod2_shift α]
      have hbr : ∀ ua : F,
          (∑ x : F × F, ∑ y : ι' → F,
            chi (Q (hEquiv.symm ((ua, x), y)) +
              ∑ i : Fin (m + 1), hEquiv.symm ((ua, x), y) (pos (i, 0)) *
                hEquiv.symm ((ua, x), y) (pos (i, 1)) * hEquiv.symm ((ua, x), y) (pos (i, 2)))) =
          Sbranch ua := by
        intro ua
        rw [Fintype.sum_prod_type]
        dsimp [Sbranch, hEquiv]
        apply Finset.sum_congr rfl; intro ub _
        apply Finset.sum_congr rfl; intro uc _
        apply Finset.sum_congr rfl; intro yr _
        rw [hg_embed, hQ_decomp]
        congr 1; ring
      rw [hbr α, hbr (α + 1)]

    have hB1 : 4 ^ m * (Sbranch α).natAbs ≤ 4 * Fintype.card (ι' → F) * 3 ^ m := by
      dsimp [Sbranch]
      let inner1 : F → F → ℤ := fun ub uc =>
        ∑ yr : ι' → F, chi ((α + α) * ub * uc + ub * Lb α yr + uc * Lc α yr + R α yr + gRest yr)
      have htri : (∑ ub : F, ∑ uc : F, inner1 ub uc).natAbs ≤
          ∑ ub : F, ∑ uc : F, (inner1 ub uc).natAbs := by
        calc (∑ ub : F, ∑ uc : F, inner1 ub uc).natAbs
            ≤ ∑ ub : F, (∑ uc : F, inner1 ub uc).natAbs := natAbs_sum_le _ _
          _ ≤ ∑ ub : F, ∑ uc : F, (inner1 ub uc).natAbs :=
              Finset.sum_le_sum (fun ub _ => natAbs_sum_le _ _)
      have hterm : ∀ ub uc : F, 4 ^ m * (inner1 ub uc).natAbs ≤ Fintype.card (ι' → F) * 3 ^ m := by
        intro ub uc
        have hq : IsQuad (fun yr => ub * Lb α yr + uc * Lc α yr + R α yr) := by
          have ha1 : IsQuad (fun yr => ub * Lb α yr) := isQuad_of_isAffine (by
            obtain ⟨v, c1, hv⟩ := hLb_aff α
            exact ⟨fun x => ub * v x, ub * c1, fun yr => by
              dsimp only; rw [hv yr, mul_add, Finset.mul_sum]
              congr 1; apply Finset.sum_congr rfl; intro x _; ring⟩)
          have ha2 : IsQuad (fun yr => uc * Lc α yr) := isQuad_of_isAffine (by
            obtain ⟨v, c1, hv⟩ := hLc_aff α
            exact ⟨fun x => uc * v x, uc * c1, fun yr => by
              dsimp only; rw [hv yr, mul_add, Finset.mul_sum]
              congr 1; apply Finset.sum_congr rfl; intro x _; ring⟩)
          exact isQuad_add (isQuad_add ha1 ha2) (hR_quad α)
        have hih := ih pos' _ hq
        have heq : inner1 ub uc =
            ∑ yr : ι' → F, chi ((ub * Lb α yr + uc * Lc α yr + R α yr) + gRest yr) := by
          dsimp [inner1]
          apply Finset.sum_congr rfl; intro yr _
          rw [zmod2_add_self, zero_mul, zero_mul, zero_add]
        rw [heq]
        exact hih
      calc 4 ^ m * (∑ ub : F, ∑ uc : F, inner1 ub uc).natAbs
          ≤ 4 ^ m * ∑ ub : F, ∑ uc : F, (inner1 ub uc).natAbs := Nat.mul_le_mul_left _ htri
        _ = ∑ ub : F, ∑ uc : F, 4 ^ m * (inner1 ub uc).natAbs := by
            simp only [Finset.mul_sum]
        _ ≤ ∑ _ub : F, ∑ _uc : F, Fintype.card (ι' → F) * 3 ^ m :=
            Finset.sum_le_sum (fun ub _ => Finset.sum_le_sum (fun uc _ => hterm ub uc))
        _ = 4 * Fintype.card (ι' → F) * 3 ^ m := by
            simp only [Finset.sum_const, Finset.card_univ, ZMod.card 2, smul_eq_mul]; ring

    have hB2 : 4 ^ m * (Sbranch (α + 1)).natAbs ≤ 2 * Fintype.card (ι' → F) * 3 ^ m := by
      have hS2 : Sbranch (α + 1) =
          2 * ∑ yr : ι' → F, chi ((Lb (α + 1) yr * Lc (α + 1) yr + R (α + 1) yr) + gRest yr) := by
        dsimp [Sbranch]
        have hswap : ∀ (f : F → F → (ι' → F) → ℤ),
            ∑ ub : F, ∑ uc : F, ∑ yr : ι' → F, f ub uc yr =
            ∑ yr : ι' → F, ∑ ub : F, ∑ uc : F, f ub uc yr := by
          intro f
          conv_lhs => arg 2; ext ub; rw [Finset.sum_comm]
          rw [Finset.sum_comm]
        rw [hswap, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro yr _
        have hα1 : α + (α + 1) = 1 := by rw [← add_assoc, zmod2_add_self, zero_add]
        have hfac : ∀ ub uc : F,
            chi ((α + (α + 1)) * ub * uc + ub * Lb (α + 1) yr + uc * Lc (α + 1) yr + R (α + 1) yr + gRest yr) =
            chi (ub * uc + ub * Lb (α + 1) yr + uc * Lc (α + 1) yr) * chi (R (α + 1) yr + gRest yr) := by
          intro ub uc
          rw [hα1, one_mul, ← chi_add]
          congr 1; ring
        simp_rw [hfac]
        have hpull : (∑ ub : F, ∑ uc : F,
            chi (ub * uc + ub * Lb (α + 1) yr + uc * Lc (α + 1) yr) * chi (R (α + 1) yr + gRest yr)) =
            (∑ ub : F, ∑ uc : F, chi (ub * uc + ub * Lb (α + 1) yr + uc * Lc (α + 1) yr)) *
              chi (R (α + 1) yr + gRest yr) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl; intro ub _
          rw [Finset.sum_mul]
        rw [hpull, sum_chi_two_vars, mul_assoc, ← chi_add]
        congr 2; ring
      rw [hS2, Int.natAbs_mul]
      have hq : IsQuad (fun yr => Lb (α + 1) yr * Lc (α + 1) yr + R (α + 1) yr) :=
        isQuad_add (isQuad_mul_affine (hLb_aff (α + 1)) (hLc_aff (α + 1))) (hR_quad (α + 1))
      have hih := ih pos' _ hq
      have h2abs : (2 : ℤ).natAbs = 2 := rfl
      rw [h2abs]
      calc 4 ^ m * (2 * _) = 2 * (4 ^ m * _) := by ring
        _ ≤ 2 * (Fintype.card (ι' → F) * 3 ^ m) := Nat.mul_le_mul_left 2 hih
        _ = 2 * Fintype.card (ι' → F) * 3 ^ m := by ring

    have hcomb : 4 ^ m * Sfull.natAbs ≤ 6 * Fintype.card (ι' → F) * 3 ^ m := by
      rw [hS_split]
      calc 4 ^ m * (Sbranch α + Sbranch (α + 1)).natAbs
          ≤ 4 ^ m * ((Sbranch α).natAbs + (Sbranch (α + 1)).natAbs) :=
            Nat.mul_le_mul_left _ (Int.natAbs_add_le _ _)
        _ = 4 ^ m * (Sbranch α).natAbs + 4 ^ m * (Sbranch (α + 1)).natAbs := Nat.mul_add _ _ _
        _ ≤ 4 * Fintype.card (ι' → F) * 3 ^ m + 2 * Fintype.card (ι' → F) * 3 ^ m :=
            Nat.add_le_add hB1 hB2
        _ = 6 * Fintype.card (ι' → F) * 3 ^ m := by ring
    rw [hcard, pow_succ, pow_succ]
    calc 4 ^ m * 4 * Sfull.natAbs = 4 * (4 ^ m * Sfull.natAbs) := by ring
      _ ≤ 4 * (6 * Fintype.card (ι' → F) * 3 ^ m) := Nat.mul_le_mul_left 4 hcomb
      _ = 8 * Fintype.card (ι' → F) * (3 ^ m * 3) := by ring

theorem cubic_fiber_bound :
    ∀ (c : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι] (m : ℕ) (pos : Fin m × Fin 3 ↪ ι)
      (Q : (ι → F) → F), IsQuad Q →
      ∀ (eqs : Fin c → (ι → F) × F),
        let A : Finset (ι → F) :=
          Finset.univ.filter (fun y => ∀ r : Fin c, (∑ i : ι, (eqs r).1 i * y i) = (eqs r).2)
        4 ^ (m - c) * (∑ y ∈ A, chi (Q y + ∑ i : Fin m, y (pos (i, 0)) * y (pos (i, 1)) * y (pos (i, 2)))).natAbs
          ≤ A.card * 3 ^ (m - c) := by
  intro c
  induction c with
  | zero =>
    intro ι _ _ m pos Q hQ eqs
    simp only [Nat.sub_zero]
    have hA : Finset.univ.filter (fun y : ι → F => ∀ r : Fin 0, (∑ i : ι, (eqs r).1 i * y i) = (eqs r).2) =
        Finset.univ := by
      ext y; simp
    rw [hA, Finset.card_univ]
    exact cubic_bound_unconstrained m pos Q hQ
  | succ c ih =>
    intro ι _ _ m pos Q hQ eqs
    dsimp only
    set A : Finset (ι → F) :=
      Finset.univ.filter (fun y => ∀ r : Fin (c + 1), (∑ i : ι, (eqs r).1 i * y i) = (eqs r).2)
    let v : ι → F := (eqs (Fin.last c)).1
    let γ : F := (eqs (Fin.last c)).2
    by_cases hv0 : ∀ i : ι, v i = 0
    · by_cases hγ : γ = 0
      · let eqs' : Fin c → (ι → F) × F := fun r => eqs r.castSucc
        have hAeq : A = Finset.univ.filter (fun y => ∀ r : Fin c, (∑ i : ι, (eqs' r).1 i * y i) = (eqs' r).2) := by
          ext y
          simp only [A, eqs', Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · intro h r; exact h r.castSucc
          · intro h r
            refine Fin.lastCases ?_ (fun r0 => h r0) r
            change (∑ i : ι, v i * y i) = γ
            rw [hγ]
            exact Finset.sum_eq_zero (fun i _ => by rw [hv0 i, zero_mul])
        rw [hAeq]
        exact pow_three_four_mono (by omega : m - (c + 1) ≤ m - c) _ _ (ih m pos Q hQ eqs')
      · have hAempty : A = ∅ := by
          ext y
          simp only [A, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
          intro h
          have hlast : (∑ i : ι, v i * y i) = γ := h (Fin.last c)
          have hzero : (∑ i : ι, v i * y i) = 0 :=
            Finset.sum_eq_zero (fun i _ => by rw [hv0 i, zero_mul])
          rw [hzero] at hlast
          exact hγ hlast.symm
        rw [hAempty]; simp
    · push Not at hv0
      obtain ⟨p, hpne⟩ := hv0
      have hp1 : v p = 1 := zmod2_eq_one_of_ne_zero hpne
      let ι1 := {x : ι // x ≠ p}
      let L : (ι1 → F) → F := fun yr => γ + ∑ x : ι1, v x.1 * yr x
      let lift : (ι1 → F) → (ι → F) := fun yr i => if h : i = p then L yr else yr ⟨i, h⟩
      have hlift_p : ∀ yr, lift yr p = L yr := fun yr => by simp [lift]
      have hlift_ne : ∀ yr (x : ι1), lift yr x.1 = yr x := fun yr x => by simp [lift, x.2]
      have hsum_split : ∀ (f : ι → F), ∑ i : ι, f i = f p + ∑ x : ι1, f x.1 := by
        intro f
        rw [← Finset.sum_add_sum_compl ({p} : Finset ι) f, Finset.sum_singleton]
        congr 1
        symm
        refine Finset.sum_bij (fun (x : ι1) _ => x.1) ?_ ?_ ?_ ?_
        · intro x _; simp [x.2]
        · intro x1 _ x2 _ h; exact Subtype.ext h
        · intro i hi
          simp only [Finset.mem_compl, Finset.mem_singleton] at hi
          exact ⟨⟨i, hi⟩, Finset.mem_univ _, rfl⟩
        · intro _ _; rfl
      let eqs1 : Fin c → (ι1 → F) × F := fun r =>
        (fun x => (eqs r.castSucc).1 x.1 + (eqs r.castSucc).1 p * v x.1,
         (eqs r.castSucc).2 + (eqs r.castSucc).1 p * γ)
      let A1 : Finset (ι1 → F) :=
        Finset.univ.filter (fun yr => ∀ r : Fin c, (∑ x : ι1, (eqs1 r).1 x * yr x) = (eqs1 r).2)
      have hlift_eq_iff : ∀ yr (r : Fin c),
          (∑ i : ι, (eqs r.castSucc).1 i * lift yr i) = (eqs r.castSucc).2 ↔
          (∑ x : ι1, (eqs1 r).1 x * yr x) = (eqs1 r).2 := by
        intro yr r
        rw [hsum_split, hlift_p]
        simp_rw [hlift_ne]
        dsimp [eqs1, L]
        have h1 : (eqs r.castSucc).1 p * (γ + ∑ x : ι1, v x.1 * yr x) +
            ∑ x : ι1, (eqs r.castSucc).1 x.1 * yr x =
            (∑ x : ι1, ((eqs r.castSucc).1 x.1 + (eqs r.castSucc).1 p * v x.1) * yr x) +
              (eqs r.castSucc).1 p * γ := by
          rw [mul_add, Finset.mul_sum]
          have hadd : (∑ x : ι1, (eqs r.castSucc).1 p * (v x.1 * yr x)) +
              (∑ x : ι1, (eqs r.castSucc).1 x.1 * yr x) =
              ∑ x : ι1, ((eqs r.castSucc).1 x.1 + (eqs r.castSucc).1 p * v x.1) * yr x := by
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl; intro x _; ring
          calc (eqs r.castSucc).1 p * γ + (∑ x : ι1, (eqs r.castSucc).1 p * (v x.1 * yr x)) +
                ∑ x : ι1, (eqs r.castSucc).1 x.1 * yr x
              = ((∑ x : ι1, (eqs r.castSucc).1 p * (v x.1 * yr x)) +
                  ∑ x : ι1, (eqs r.castSucc).1 x.1 * yr x) + (eqs r.castSucc).1 p * γ := by ring
            _ = _ := by rw [hadd]
        rw [h1]
        constructor
        · intro h
          calc ∑ x : ι1, ((eqs r.castSucc).1 x.1 + (eqs r.castSucc).1 p * v x.1) * yr x
              = ((∑ x : ι1, ((eqs r.castSucc).1 x.1 + (eqs r.castSucc).1 p * v x.1) * yr x) +
                  (eqs r.castSucc).1 p * γ) + (eqs r.castSucc).1 p * γ := by
                rw [add_assoc, zmod2_add_self, add_zero]
            _ = (eqs r.castSucc).2 + (eqs r.castSucc).1 p * γ := by rw [h]
        · intro h
          rw [h, add_assoc, zmod2_add_self, add_zero]
      have hlift_last : ∀ yr, (∑ i : ι, v i * lift yr i) = γ := by
        intro yr
        rw [hsum_split, hlift_p, hp1, one_mul]
        simp_rw [hlift_ne]
        dsimp [L]
        rw [add_assoc, zmod2_add_self, add_zero]
      have hlift_bij : ∀ (f : (ι → F) → ℤ), ∑ y ∈ A, f y = ∑ yr ∈ A1, f (lift yr) := by
        intro f
        symm
        refine Finset.sum_bij (fun yr _ => lift yr) ?_ ?_ ?_ ?_
        · intro yr hyr
          simp only [A1, Finset.mem_filter, Finset.mem_univ, true_and] at hyr
          simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
          intro r
          refine Fin.lastCases (hlift_last yr) (fun r0 => (hlift_eq_iff yr r0).mpr (hyr r0)) r
        · intro yr1 _ yr2 _ h
          funext x
          have := congrFun h x.1
          simpa [lift, x.2] using this
        · intro y hy
          simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hy
          let yr : ι1 → F := fun x => y x.1
          have hlast : (∑ i : ι, v i * y i) = γ := hy (Fin.last c)
          rw [hsum_split, hp1, one_mul] at hlast
          have hyp : y p = L yr := by
            dsimp [L, yr]
            calc y p = (y p + ∑ x : ι1, v x.1 * y x.1) + ∑ x : ι1, v x.1 * y x.1 := by
                  rw [add_assoc, zmod2_add_self, add_zero]
              _ = γ + ∑ x : ι1, v x.1 * y x.1 := by rw [hlast]
          have hly : lift yr = y := by
            funext i
            dsimp [lift, yr]
            split_ifs with hi
            · subst hi; exact hyp.symm
            · rfl
          have hyr_mem : yr ∈ A1 := by
            simp only [A1, Finset.mem_filter, Finset.mem_univ, true_and]
            intro r
            exact (hlift_eq_iff yr r).mp (by rw [hly]; exact hy r.castSucc)
          exact ⟨yr, hyr_mem, hly⟩
        · intro _ _; rfl
      have hcardA : A.card = A1.card := by
        have h1 := hlift_bij (fun _ => (1 : ℤ))
        simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h1
        exact Int.ofNat.inj h1
      have hQ1 : IsQuad (fun yr => Q (lift yr)) := by
        apply isQuad_comp_affine hQ
        intro i
        dsimp [lift]
        split_ifs with hi
        · exact ⟨fun x => v x.1, γ, fun _ => by dsimp [L]; ring⟩
        · exact ⟨fun x => if x = ⟨i, hi⟩ then 1 else 0, 0, fun yr => by simp⟩
      by_cases hp_in : ∃ i0 : Fin m, ∃ t0 : Fin 3, pos (i0, t0) = p
      · obtain ⟨i0, t0, hpos0⟩ := hp_in
        have hm1 : 0 < m := Fin.pos i0
        let t1 : Fin 3 := ⟨(t0.val + 1) % 3, Nat.mod_lt _ (by decide)⟩
        let t2 : Fin 3 := ⟨(t0.val + 2) % 3, Nat.mod_lt _ (by decide)⟩
        have ht01 : t0 ≠ t1 := by fin_cases t0 <;> decide
        have ht02 : t0 ≠ t2 := by fin_cases t0 <;> decide
        have ht12 : t1 ≠ t2 := by fin_cases t0 <;> decide
        have htriple_prod : ∀ y : ι → F,
            y (pos (i0, 0)) * y (pos (i0, 1)) * y (pos (i0, 2)) =
            y (pos (i0, t0)) * y (pos (i0, t1)) * y (pos (i0, t2)) := by
          intro y; fin_cases t0 <;> dsimp [t1, t2] <;> ring
        have hp1_ne : pos (i0, t1) ≠ p := fun h => by
          rw [← hpos0] at h
          exact ht01 (congrArg Prod.snd (pos.injective h)).symm
        have hp2_ne : pos (i0, t2) ≠ p := fun h => by
          rw [← hpos0] at h
          exact ht02 (congrArg Prod.snd (pos.injective h)).symm
        let p1' : ι1 := ⟨pos (i0, t1), hp1_ne⟩
        let p2' : ι1 := ⟨pos (i0, t2), hp2_ne⟩
        have hp12' : p2' ≠ p1' := fun h =>
          ht12 (congrArg Prod.snd (pos.injective (congrArg Subtype.val h))).symm
        let ι2 := {x : ι1 // x ≠ p1'}
        let lift2 (β : F) (z : ι2 → F) : ι1 → F := fun x => if h : x = p1' then β else z ⟨x, h⟩
        let eqs2 (β : F) : Fin c → (ι2 → F) × F := fun r =>
          (fun x => (eqs1 r).1 x.1, (eqs1 r).2 + (eqs1 r).1 p1' * β)
        let A2 (β : F) : Finset (ι2 → F) :=
          Finset.univ.filter (fun z => ∀ r : Fin c, (∑ x : ι2, (eqs2 β r).1 x * z x) = (eqs2 β r).2)
        have hsum1_split : ∀ (f : ι1 → F), ∑ x : ι1, f x = f p1' + ∑ x : ι2, f x.1 := by
          intro f
          rw [← Finset.sum_add_sum_compl ({p1'} : Finset ι1) f, Finset.sum_singleton]
          congr 1
          symm
          refine Finset.sum_bij (fun (x : ι2) _ => x.1) ?_ ?_ ?_ ?_
          · intro x _; simp [x.2]
          · intro x1 _ x2 _ h; exact Subtype.ext h
          · intro i hi
            simp only [Finset.mem_compl, Finset.mem_singleton] at hi
            exact ⟨⟨i, hi⟩, Finset.mem_univ _, rfl⟩
          · intro _ _; rfl
        have hA1_split : ∀ (f : (ι1 → F) → ℤ),
            ∑ yr ∈ A1, f yr = (∑ z ∈ A2 0, f (lift2 0 z)) + (∑ z ∈ A2 1, f (lift2 1 z)) := by
          intro f
          have hpart : ∑ yr ∈ A1, f yr =
              (∑ yr ∈ A1.filter (fun yr => yr p1' = 0), f yr) +
              (∑ yr ∈ A1.filter (fun yr => yr p1' ≠ 0), f yr) :=
            (Finset.sum_filter_add_sum_filter_not A1 (fun yr => yr p1' = 0) f).symm
          rw [hpart]
          have hbij : ∀ (β : F),
              ∑ yr ∈ A1.filter (fun yr => yr p1' = β), f yr = ∑ z ∈ A2 β, f (lift2 β z) := by
            intro β
            symm
            refine Finset.sum_bij (fun z _ => lift2 β z) ?_ ?_ ?_ ?_
            · intro z hz
              simp only [A2, Finset.mem_filter, Finset.mem_univ, true_and] at hz
              simp only [A1, Finset.mem_filter, Finset.mem_univ, true_and]
              refine ⟨fun r => ?_, by simp [lift2]⟩
              rw [hsum1_split]
              have hval1 : lift2 β z p1' = β := by simp [lift2]
              have hval2 : ∀ x : ι2, lift2 β z x.1 = z x := fun x => by simp [lift2, x.2]
              rw [hval1]
              simp_rw [hval2]
              have hzr := hz r
              dsimp [eqs2] at hzr
              rw [hzr]
              calc (eqs1 r).1 p1' * β + ((eqs1 r).2 + (eqs1 r).1 p1' * β)
                  = (eqs1 r).2 + ((eqs1 r).1 p1' * β + (eqs1 r).1 p1' * β) := by ring
                _ = (eqs1 r).2 := by rw [zmod2_add_self, add_zero]
            · intro z1 _ z2 _ h
              funext x
              have := congrFun h x.1
              simpa [lift2, x.2] using this
            · intro yr hyr
              simp only [A1, Finset.mem_filter, Finset.mem_univ, true_and] at hyr
              let z : ι2 → F := fun x => yr x.1
              have hz_mem : z ∈ A2 β := by
                simp only [A2, Finset.mem_filter, Finset.mem_univ, true_and]
                intro r
                have hr := hyr.1 r
                rw [hsum1_split, hyr.2] at hr
                dsimp [eqs2, z]
                calc ∑ x : ι2, (eqs1 r).1 x.1 * yr x.1
                    = ((eqs1 r).1 p1' * β + ∑ x : ι2, (eqs1 r).1 x.1 * yr x.1) + (eqs1 r).1 p1' * β := by
                      rw [add_comm ((eqs1 r).1 p1' * β), add_assoc, zmod2_add_self, add_zero]
                  _ = (eqs1 r).2 + (eqs1 r).1 p1' * β := by rw [hr]
              refine ⟨z, hz_mem, ?_⟩
              funext x
              dsimp [lift2, z]
              split_ifs with hx
              · subst hx; exact hyr.2.symm
              · rfl
            · intro _ _; rfl
          have hne_eq : A1.filter (fun yr => yr p1' ≠ 0) = A1.filter (fun yr => yr p1' = 1) := by
            ext yr
            simp only [Finset.mem_filter]
            exact ⟨fun ⟨h1, h2⟩ => ⟨h1, zmod2_eq_one_of_ne_zero h2⟩,
                   fun ⟨h1, h2⟩ => ⟨h1, by rw [h2]; decide⟩⟩
          rw [hne_eq, hbij 0, hbij 1]
        have hcardA1 : A1.card = (A2 0).card + (A2 1).card := by
          have h1 := hA1_split (fun _ => (1 : ℤ))
          simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h1
          omega

        let m' := m - 1
        have hm' : m' + 1 = m := Nat.sub_add_cancel hm1
        let i0' : Fin (m' + 1) := Fin.cast hm'.symm i0
        let skipIdx : Fin m' ↪ Fin m :=
          ⟨fun j => Fin.cast hm' (i0'.succAbove j),
           fun j1 j2 h => Fin.succAbove_right_injective (p := i0') (Fin.cast_injective hm' h)⟩
        have hskip_ne : ∀ j : Fin m', skipIdx j ≠ i0 := by
          intro j h
          have h' : i0'.succAbove j = i0' := by
            apply Fin.cast_injective hm'
            change Fin.cast hm' (i0'.succAbove j) = i0 at h
            rw [h]; simp [i0']
          exact Fin.succAbove_ne i0' j h'
        let pos2 : Fin m' × Fin 3 ↪ ι2 :=
          ⟨fun q => ⟨⟨pos (skipIdx q.1, q.2), fun h => by
            rw [← hpos0] at h
            exact hskip_ne q.1 (Prod.mk.inj (pos.injective h)).1⟩, fun h => by
            have h' : pos (skipIdx q.1, q.2) = pos (i0, t1) := congrArg Subtype.val h
            exact hskip_ne q.1 (Prod.mk.inj (pos.injective h')).1⟩,
           fun q1 q2 h => by
            have h1 : pos (skipIdx q1.1, q1.2) = pos (skipIdx q2.1, q2.2) :=
              congrArg (fun x : ι2 => x.1.1) h
            have h2 := pos.injective h1
            exact Prod.ext (skipIdx.injective (Prod.mk.inj h2).1) (Prod.mk.inj h2).2⟩
        let Q2 (β : F) (z : ι2 → F) : F :=
          Q (lift (lift2 β z)) + L (lift2 β z) * β * z ⟨p2', hp12'⟩
        have hQ2 : ∀ β : F, IsQuad (Q2 β) := by
          intro β
          have hlift2_aff : ∀ x : ι1, IsAffine (fun z : ι2 → F => lift2 β z x) := by
            intro x
            dsimp [lift2]
            split_ifs with hx
            · exact ⟨fun _ => 0, β, fun _ => by simp⟩
            · exact ⟨fun w => if w = ⟨x, hx⟩ then 1 else 0, 0, fun z => by simp⟩
          have hQ_part : IsQuad (fun z => Q (lift (lift2 β z))) :=
            isQuad_comp_affine hQ1 hlift2_aff
          have hL_part : IsAffine (fun z => L (lift2 β z) * β) := by
            refine ⟨fun w => v w.1.1 * β, (γ + v p1'.1 * β) * β, fun z => ?_⟩
            dsimp only [L]
            rw [hsum1_split]
            have h1 : lift2 β z p1' = β := by simp [lift2]
            have h2 : ∀ w : ι2, lift2 β z w.1 = z w := fun w => by simp [lift2, w.2]
            rw [h1]
            simp_rw [h2]
            rw [add_mul, add_mul, Finset.sum_mul]
            have h3 : (∑ w : ι2, v w.1.1 * z w * β) = ∑ w : ι2, v w.1.1 * β * z w :=
              Finset.sum_congr rfl (fun w _ => by ring)
            rw [h3]; ring
          have hz_aff : IsAffine (fun z : ι2 → F => z ⟨p2', hp12'⟩) :=
            ⟨fun w => if w = ⟨p2', hp12'⟩ then 1 else 0, 0, fun z => by simp⟩
          exact isQuad_add hQ_part (isQuad_mul_affine hL_part hz_aff)
        have hg_split : ∀ (β : F) (z : ι2 → F),
            Q (lift (lift2 β z)) +
              (∑ i : Fin m, lift (lift2 β z) (pos (i, 0)) * lift (lift2 β z) (pos (i, 1)) * lift (lift2 β z) (pos (i, 2))) =
            Q2 β z + ∑ j : Fin m', z (pos2 (j, 0)) * z (pos2 (j, 1)) * z (pos2 (j, 2)) := by
          intro β z
          let y := lift (lift2 β z)
          have hsum_i : ∑ i : Fin m, y (pos (i, 0)) * y (pos (i, 1)) * y (pos (i, 2)) =
              y (pos (i0, 0)) * y (pos (i0, 1)) * y (pos (i0, 2)) +
              ∑ j : Fin m', y (pos (skipIdx j, 0)) * y (pos (skipIdx j, 1)) * y (pos (skipIdx j, 2)) := by
            rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i0)]
            congr 1
            symm
            refine Finset.sum_bij (fun j _ => skipIdx j) ?_ ?_ ?_ ?_
            · intro j _; exact Finset.mem_erase.mpr ⟨hskip_ne j, Finset.mem_univ _⟩
            · intro j1 _ j2 _ h; exact skipIdx.injective h
            · intro i hi
              have hne : Fin.cast hm'.symm i ≠ i0' := fun h =>
                (Finset.mem_erase.mp hi).1 (by
                  have h1 := congrArg (Fin.cast hm') h
                  simpa [i0'] using h1)
              obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hne
              refine ⟨j, Finset.mem_univ _, ?_⟩
              show Fin.cast hm' (i0'.succAbove j) = i
              rw [hj]; simp
            · intro _ _; rfl
          rw [hsum_i, htriple_prod y]
          have hy0 : y (pos (i0, t0)) = L (lift2 β z) := by
            dsimp [y]; rw [hpos0, hlift_p]
          have hy1 : y (pos (i0, t1)) = β := by
            dsimp [y]
            have : lift (lift2 β z) p1'.1 = lift2 β z p1' := hlift_ne (lift2 β z) p1'
            change lift (lift2 β z) p1'.1 = β
            rw [this]; simp [lift2]
          have hy2 : y (pos (i0, t2)) = z ⟨p2', hp12'⟩ := by
            dsimp [y]
            have : lift (lift2 β z) p2'.1 = lift2 β z p2' := hlift_ne (lift2 β z) p2'
            change lift (lift2 β z) p2'.1 = z ⟨p2', hp12'⟩
            rw [this]; simp [lift2, hp12']
          have hrest : ∀ j : Fin m', ∀ t : Fin 3, y (pos (skipIdx j, t)) = z (pos2 (j, t)) := by
            intro j t
            dsimp [y]
            have h1 : lift (lift2 β z) (pos2 (j, t)).1.1 = lift2 β z (pos2 (j, t)).1 :=
              hlift_ne (lift2 β z) (pos2 (j, t)).1
            change lift (lift2 β z) (pos2 (j, t)).1.1 = z (pos2 (j, t))
            rw [h1]; simp [lift2, (pos2 (j, t)).2]
          rw [hy0, hy1, hy2]
          simp_rw [hrest]
          dsimp [Q2]; ring
        have hsub : m' - c = m - (c + 1) := by dsimp [m']; omega
        have hih0 := ih m' pos2 (Q2 0) (hQ2 0) (eqs2 0)
        have hih1 := ih m' pos2 (Q2 1) (hQ2 1) (eqs2 1)
        rw [hsub] at hih0 hih1
        rw [hlift_bij, hA1_split, hcardA, hcardA1]
        let S0 : ℤ := ∑ z ∈ A2 0, chi (Q2 0 z + ∑ j : Fin m', z (pos2 (j, 0)) * z (pos2 (j, 1)) * z (pos2 (j, 2)))
        let S1 : ℤ := ∑ z ∈ A2 1, chi (Q2 1 z + ∑ j : Fin m', z (pos2 (j, 0)) * z (pos2 (j, 1)) * z (pos2 (j, 2)))
        have hsum0 : (∑ z ∈ A2 0, chi (Q (lift (lift2 0 z)) +
            ∑ i : Fin m, lift (lift2 0 z) (pos (i, 0)) * lift (lift2 0 z) (pos (i, 1)) * lift (lift2 0 z) (pos (i, 2)))) = S0 :=
          Finset.sum_congr rfl (fun z _ => by rw [hg_split 0 z])
        have hsum1 : (∑ z ∈ A2 1, chi (Q (lift (lift2 1 z)) +
            ∑ i : Fin m, lift (lift2 1 z) (pos (i, 0)) * lift (lift2 1 z) (pos (i, 1)) * lift (lift2 1 z) (pos (i, 2)))) = S1 :=
          Finset.sum_congr rfl (fun z _ => by rw [hg_split 1 z])
        rw [hsum0, hsum1]
        calc 4 ^ (m - (c + 1)) * (S0 + S1).natAbs
            ≤ 4 ^ (m - (c + 1)) * (S0.natAbs + S1.natAbs) :=
              Nat.mul_le_mul_left _ (Int.natAbs_add_le S0 S1)
          _ = 4 ^ (m - (c + 1)) * S0.natAbs + 4 ^ (m - (c + 1)) * S1.natAbs := Nat.mul_add _ _ _
          _ ≤ (A2 0).card * 3 ^ (m - (c + 1)) + (A2 1).card * 3 ^ (m - (c + 1)) :=
              Nat.add_le_add hih0 hih1
          _ = ((A2 0).card + (A2 1).card) * 3 ^ (m - (c + 1)) := by ring
      · let pos1 : Fin m × Fin 3 ↪ ι1 :=
          ⟨fun q => ⟨pos q, fun h => hp_in ⟨q.1, q.2, h⟩⟩,
           fun q1 q2 h => pos.injective (congrArg Subtype.val h)⟩
        rw [hlift_bij, hcardA]
        have hsum_eq : (∑ yr ∈ A1, chi (Q (lift yr) +
            ∑ i : Fin m, lift yr (pos (i, 0)) * lift yr (pos (i, 1)) * lift yr (pos (i, 2)))) =
            ∑ yr ∈ A1, chi (Q (lift yr) + ∑ i : Fin m, yr (pos1 (i, 0)) * yr (pos1 (i, 1)) * yr (pos1 (i, 2))) := by
          apply Finset.sum_congr rfl; intro yr _
          congr 2; apply Finset.sum_congr rfl; intro i _
          have h0 : lift yr (pos (i, 0)) = yr (pos1 (i, 0)) := hlift_ne yr (pos1 (i, 0))
          have h1 : lift yr (pos (i, 1)) = yr (pos1 (i, 1)) := hlift_ne yr (pos1 (i, 1))
          have h2 : lift yr (pos (i, 2)) = yr (pos1 (i, 2)) := hlift_ne yr (pos1 (i, 2))
          rw [h0, h1, h2]
        rw [hsum_eq]
        exact pow_three_four_mono (by omega : m - (c + 1) ≤ m - c) _ _ (ih m pos1 (fun yr => Q (lift yr)) hQ1 eqs1)

def legalGate (h : Gate) : Prop :=
  h.inputs.length ≤ 2 ∧
    (h.op = .and ∨ h.op = .or ∨ h.op = .mod 2 ∨ (h.op = .not ∧ h.inputs.length = 1))

def isPaid (h : Gate) : Bool :=
  @decide ((h.op = .and ∨ h.op = .or) ∧ h.inputs.length = 2) (Classical.propDecidable _)

def circuitCost (C : Circuit) : ℕ := C.gates.countP isPaid

def legalCirc (n : ℕ) (C : Circuit) : Prop :=
  ReadsBack n C ∧ ∀ h ∈ C.gates, legalGate h

def bitsVec (n : ℕ) (u : Fin n → F) : List Bool :=
  List.ofFn (fun j : Fin n => decide (u j = 1))

def wireList (gs : List Gate) (inp : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) inp

lemma wireList_append (gs1 gs2 : List Gate) (inp : List Bool) :
    wireList (gs1 ++ gs2) inp = wireList gs2 (wireList gs1 inp) := by
  simp [wireList, List.foldl_append]

lemma wireList_length (gs : List Gate) (inp : List Bool) :
    (wireList gs inp).length = inp.length + gs.length := by
  induction gs generalizing inp with
  | nil => simp [wireList]
  | cons g rest ih =>
    simp only [wireList, List.foldl_cons] at ih ⊢
    rw [ih]
    simp; omega

lemma getD_append_lt {w v : List Bool} {i : ℕ} (hi : i < w.length) :
    (w ++ v).getD i false = w.getD i false := by
  have hi' : i < (w ++ v).length := by simp; omega
  rw [List.getD_eq_getElem _ _ hi', List.getD_eq_getElem _ _ hi, List.getElem_append_left hi]

lemma wireList_getD_lt (gs : List Gate) (inp : List Bool) (i : ℕ) (hi : i < inp.length) :
    (wireList gs inp).getD i false = inp.getD i false := by
  induction gs generalizing inp with
  | nil => rfl
  | cons g rest ih =>
    have hstep : wireList (g :: rest) inp =
        wireList rest (inp ++ [g.op.eval (g.inputs.map fun idx => inp.getD idx false)]) := rfl
    rw [hstep]
    have hi' : i < (inp ++ [g.op.eval (g.inputs.map fun idx => inp.getD idx false)]).length := by
      simp; omega
    rw [ih _ hi', getD_append_lt hi]

lemma wireList_snoc_last (gs : List Gate) (g : Gate) (inp : List Bool) :
    (wireList (gs ++ [g]) inp).getD (inp.length + gs.length) false =
      g.op.eval (g.inputs.map fun idx => (wireList gs inp).getD idx false) := by
  rw [wireList_append]
  simp only [wireList, List.foldl_cons, List.foldl_nil]
  let w := List.foldl (fun w g => w ++ [g.op.eval (List.map (fun i => w.getD i false) g.inputs)]) inp gs
  let v := g.op.eval (List.map (fun idx => w.getD idx false) g.inputs)
  have hlen : w.length = inp.length + gs.length := wireList_length gs inp
  have hlt : w.length < (w ++ [v]).length := by simp
  change (w ++ [v]).getD (inp.length + gs.length) false = v
  rw [← hlen, List.getD_eq_getElem _ _ hlt, List.getElem_append_right (Nat.le_refl _)]
  simp

lemma gate_eval_paid {h : Gate} (hpaid : isPaid h = true) :
    ∃ a b : ℕ, h.inputs = [a, b] ∧ (h.op = .and ∨ h.op = .or) := by
  have hp : (h.op = .and ∨ h.op = .or) ∧ h.inputs.length = 2 := by
    simpa [isPaid] using hpaid
  match h_in : h.inputs with
  | [a, b] => exact ⟨a, b, rfl, hp.1⟩
  | [] | [_] | _ :: _ :: _ :: _ =>
    have := hp.2; simp [h_in] at this

def AffSet {k c : ℕ} (eqs : Fin c → (Fin k → F) × F) : Finset (Fin k → F) :=
  Finset.univ.filter (fun y => ∀ r : Fin c, (∑ i : Fin k, (eqs r).1 i * y i) = (eqs r).2)

structure AffLeaf (k nw : ℕ) where
  c : ℕ
  eqs : Fin c → (Fin k → F) × F
  lin : Fin nw → (Fin k → F) × F

lemma circuit_affine_partition (k : ℕ) :
    ∀ (gs : List Gate),
      (∀ j < gs.length, ∀ idx ∈ (gs.getD j ⟨.or, []⟩).inputs, idx < k + j) →
      (∀ h ∈ gs, legalGate h) →
      ∀ (l : ℕ) (eqs0 : Fin l → (Fin k → F) × F),
        ∃ leaves : List (AffLeaf k (k + gs.length)),
          (∀ lf ∈ leaves, lf.c ≤ l + gs.countP isPaid) ∧
          (∀ y : Fin k → F, y ∈ AffSet eqs0 →
            ∃! idx : Fin leaves.length, y ∈ AffSet (leaves.get idx).eqs) ∧
          (∀ lf ∈ leaves, ∀ y ∈ AffSet lf.eqs, y ∈ AffSet eqs0) ∧
          (∀ lf ∈ leaves, ∀ y ∈ AffSet lf.eqs,
            ∀ w : Fin (k + gs.length),
              b2z ((wireList gs (bitsVec k y)).getD w.val false) =
                (∑ i : Fin k, (lf.lin w).1 i * y i) + (lf.lin w).2) := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil =>
    intro _ _ l eqs0
    simp only [List.countP_nil, add_zero, List.length_nil]
    let leaf0 : AffLeaf k k :=
      { c := l
        eqs := eqs0
        lin := fun w => (fun i => if i = w then 1 else 0, 0) }
    refine ⟨[leaf0], ?_, ?_, ?_, ?_⟩
    · intro lf hlf; rw [List.mem_singleton.mp hlf]
    · intro y hy
      refine ⟨⟨0, by simp⟩, hy, fun idx _ => Fin.ext (by have := idx.isLt; simp at this ⊢)⟩
    · intro lf hlf y hy
      rw [List.mem_singleton.mp hlf] at hy; exact hy
    · intro lf hlf y _ w
      rw [List.mem_singleton.mp hlf]
      dsimp [leaf0, wireList, bitsVec]
      rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn, b2z_decide_eq_one]
      simp
  | append_singleton gs g ih =>
    intro hrb hleg l eqs0
    have hrb_pre : ∀ j < gs.length, ∀ idx ∈ (gs.getD j ⟨.or, []⟩).inputs, idx < k + j := by
      intro j hj idx hidx
      have h1 := hrb j (by simp; omega) idx
      have hget : (gs ++ [g]).getD j ⟨.or, []⟩ = gs.getD j ⟨.or, []⟩ := by
        rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ hj,
          List.getElem_append_left hj]
      rw [hget] at h1
      exact h1 hidx
    have hrb_last : ∀ idx ∈ g.inputs, idx < k + gs.length := by
      intro idx hidx
      have h1 := hrb gs.length (by simp) idx
      have hget : (gs ++ [g]).getD gs.length ⟨.or, []⟩ = g := by
        rw [List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (Nat.le_refl _)]
        simp
      rw [hget] at h1
      exact h1 hidx
    have hleg_pre : ∀ h ∈ gs, legalGate h := fun h hh => hleg h (List.mem_append_left _ hh)
    have hleg_g : legalGate g := hleg g (List.mem_append_right _ (List.mem_singleton_self _))
    obtain ⟨leaves, hc_le, hpart, hsub, hsem⟩ := ih hrb_pre hleg_pre l eqs0
    have hlen_snoc : (gs ++ [g]).length = gs.length + 1 := by simp
    have hcnt_snoc : (gs ++ [g]).countP isPaid = gs.countP isPaid + if isPaid g then 1 else 0 := by
      rw [List.countP_append, List.countP_singleton]
    have hwire_pre : ∀ y (w : Fin (k + gs.length)),
        (wireList (gs ++ [g]) (bitsVec k y)).getD w.val false =
        (wireList gs (bitsVec k y)).getD w.val false := by
      intro y w
      rw [wireList_append]
      have hlt : w.val < (wireList gs (bitsVec k y)).length := by
        rw [wireList_length, bitsVec, List.length_ofFn]; exact w.isLt
      exact wireList_getD_lt [g] _ w.val hlt
    have hwire_last : ∀ y,
        (wireList (gs ++ [g]) (bitsVec k y)).getD (k + gs.length) false =
        g.op.eval (g.inputs.map fun idx => (wireList gs (bitsVec k y)).getD idx false) := by
      intro y
      have hbl : (bitsVec k y).length = k := by simp [bitsVec]
      simpa [hbl] using wireList_snoc_last gs g (bitsVec k y)
    have hfin_last : ∀ w : Fin (k + (gs ++ [g]).length), ¬ w.val < k + gs.length → w.val = k + gs.length := by
      intro w hw
      have hlt : w.val < k + (gs.length + 1) := by simpa [hlen_snoc] using w.isLt
      omega
    cases hpaid : isPaid g
    ·
      have hext : ∀ (lf : AffLeaf k (k + gs.length)),
          (∀ y ∈ AffSet lf.eqs, ∀ w : Fin (k + gs.length),
            b2z ((wireList gs (bitsVec k y)).getD w.val false) =
              (∑ i : Fin k, (lf.lin w).1 i * y i) + (lf.lin w).2) →
          ∃ newLin : (Fin k → F) × F,
            ∀ y ∈ AffSet lf.eqs,
              b2z ((wireList (gs ++ [g]) (bitsVec k y)).getD (k + gs.length) false) =
                (∑ i : Fin k, newLin.1 i * y i) + newLin.2 := by
        intro lf hlf
        match hg_in : g.inputs with
        | [] =>
          refine ⟨(fun _ => 0, b2z (g.op.eval [])), fun y _ => ?_⟩
          rw [hwire_last, hg_in]; simp
        | [a] =>
          have ha : a < k + gs.length := hrb_last a (by simp [hg_in])
          let fa : Fin (k + gs.length) := ⟨a, ha⟩
          rcases hleg_g.2 with hop | hop | hop | ⟨hop, _⟩
          · refine ⟨lf.lin fa, fun y hy => ?_⟩
            rw [hwire_last, hg_in, hop]
            simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id, Bool.and_true]
            exact hlf y hy fa
          · refine ⟨lf.lin fa, fun y hy => ?_⟩
            rw [hwire_last, hg_in, hop]
            simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id, Bool.or_false]
            exact hlf y hy fa
          · refine ⟨((lf.lin fa).1, (lf.lin fa).2 + 1), fun y hy => ?_⟩
            rw [hwire_last, hg_in, hop]
            simp only [List.map_cons, List.map_nil, b2z_mod2_single]
            rw [hlf y hy fa]; ring
          · refine ⟨((lf.lin fa).1, (lf.lin fa).2 + 1), fun y hy => ?_⟩
            rw [hwire_last, hg_in, hop]
            simp only [List.map_cons, List.map_nil, GateOp.eval, List.headD_cons, b2z_not]
            rw [hlf y hy fa]; ring
        | [a, b] =>
          have ha : a < k + gs.length := hrb_last a (by simp [hg_in])
          have hb : b < k + gs.length := hrb_last b (by simp [hg_in])
          let fa : Fin (k + gs.length) := ⟨a, ha⟩
          let fb : Fin (k + gs.length) := ⟨b, hb⟩
          rcases hleg_g.2 with hop | hop | hop | ⟨_, h1⟩
          · exfalso; simp [isPaid, hg_in, hop] at hpaid
          · exfalso; simp [isPaid, hg_in, hop] at hpaid
          · refine ⟨(fun i => (lf.lin fa).1 i + (lf.lin fb).1 i, (lf.lin fa).2 + (lf.lin fb).2 + 1), fun y hy => ?_⟩
            rw [hwire_last, hg_in, hop]
            simp only [List.map_cons, List.map_nil, b2z_mod2_pair]
            rw [hlf y hy fa, hlf y hy fb]
            simp only [add_mul, Finset.sum_add_distrib]; ring
          · simp [hg_in] at h1
        | _ :: _ :: _ :: _ =>
          have := hleg_g.1; simp [hg_in] at this
      let extLeaf (lf : AffLeaf k (k + gs.length)) : AffLeaf k (k + (gs ++ [g]).length) :=
        { c := lf.c
          eqs := lf.eqs
          lin := fun w =>
            if hw : w.val < k + gs.length then lf.lin ⟨w.val, hw⟩
            else if hlf : lf ∈ leaves then Classical.choose (hext lf (hsem lf hlf))
            else (fun _ => 0, 0) }
      let leaves' := leaves.map extLeaf
      refine ⟨leaves', ?_, ?_, ?_, ?_⟩
      · intro lf' hlf'
        obtain ⟨lf, hlf, rfl⟩ := List.mem_map.mp hlf'
        have hc := hc_le lf hlf
        dsimp [extLeaf]; rw [hcnt_snoc, hpaid]; simp; exact hc
      · intro y hy
        obtain ⟨idx, hmem, huniq⟩ := hpart y hy
        have hlen' : leaves'.length = leaves.length := by simp [leaves']
        refine ⟨⟨idx.val, by omega⟩, ?_, ?_⟩
        · dsimp only
          have hget : leaves'.get ⟨idx.val, by omega⟩ = extLeaf (leaves.get idx) := by
            simp [leaves', List.get_eq_getElem]
          rw [hget]
          exact hmem
        · intro idx2 hmem2
          have hlt2 : idx2.val < leaves.length := by have := idx2.isLt; omega
          have hget : leaves'.get idx2 = extLeaf (leaves.get ⟨idx2.val, hlt2⟩) := by
            simp [leaves', List.get_eq_getElem]
          rw [hget] at hmem2
          have heq := huniq ⟨idx2.val, hlt2⟩ hmem2
          exact Fin.ext (show idx2.val = idx.val from congrArg Fin.val heq)
      · intro lf' hlf' y hy
        obtain ⟨lf, hlf, rfl⟩ := List.mem_map.mp hlf'
        exact hsub lf hlf y hy
      · intro lf' hlf' y hy w
        obtain ⟨lf, hlf, rfl⟩ := List.mem_map.mp hlf'
        dsimp [extLeaf] at hy ⊢
        by_cases hw : w.val < k + gs.length
        · simp only [hw, ↓reduceDIte]
          have := hwire_pre y ⟨w.val, hw⟩
          dsimp at this; rw [this]
          exact hsem lf hlf y hy ⟨w.val, hw⟩
        · simp only [hw, hlf, ↓reduceDIte]
          rw [hfin_last w hw]
          exact Classical.choose_spec (hext lf (hsem lf hlf)) y hy
    ·
      obtain ⟨a, b, hgab, hop_ab⟩ := gate_eval_paid hpaid
      have ha : a < k + gs.length := hrb_last a (by simp [hgab])
      have hb : b < k + gs.length := hrb_last b (by simp [hgab])
      let fa : Fin (k + gs.length) := ⟨a, ha⟩
      let fb : Fin (k + gs.length) := ⟨b, hb⟩
      let mkChild (lf : AffLeaf k (k + gs.length)) (γ : F) : AffLeaf k (k + (gs ++ [g]).length) :=
        let newL : (Fin k → F) × F :=
          if g.op = .and then
            if γ = 0 then (fun _ => 0, 0) else lf.lin fb
          else
            if γ = 0 then lf.lin fb else (fun _ => 0, 1)
        { c := lf.c + 1
          eqs := Fin.snoc lf.eqs ((lf.lin fa).1, (lf.lin fa).2 + γ)
          lin := fun w => if hw : w.val < k + gs.length then lf.lin ⟨w.val, hw⟩ else newL }
      have hchild_mem : ∀ (lf : AffLeaf k (k + gs.length)) (γ : F) (y : Fin k → F),
          y ∈ AffSet (mkChild lf γ).eqs ↔
          y ∈ AffSet lf.eqs ∧ (∑ i : Fin k, (lf.lin fa).1 i * y i) + (lf.lin fa).2 = γ := by
        intro lf γ y
        dsimp [mkChild]
        simp only [AffSet, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro h
          refine ⟨fun r => by simpa [Fin.snoc_castSucc] using h r.castSucc, ?_⟩
          have hl := h (Fin.last lf.c)
          simp only [Fin.snoc_last] at hl
          rw [hl]
          calc (lf.lin fa).2 + γ + (lf.lin fa).2
              = γ + ((lf.lin fa).2 + (lf.lin fa).2) := by ring
            _ = γ := by rw [zmod2_add_self, add_zero]
        · rintro ⟨h1, h2⟩ r
          refine Fin.lastCases ?_ (fun r0 => by simpa [Fin.snoc_castSucc] using h1 r0) r
          simp only [Fin.snoc_last]
          calc ∑ i : Fin k, (lf.lin fa).1 i * y i
              = ((∑ i : Fin k, (lf.lin fa).1 i * y i) + (lf.lin fa).2) + (lf.lin fa).2 := by
                rw [add_assoc, zmod2_add_self, add_zero]
            _ = γ + (lf.lin fa).2 := by rw [h2]
            _ = (lf.lin fa).2 + γ := add_comm _ _
      let splitFun : AffLeaf k (k + gs.length) → List (AffLeaf k (k + (gs ++ [g]).length)) :=
        fun lf => [mkChild lf 0, mkChild lf 1]
      let leaves' := leaves.flatMap splitFun
      refine ⟨leaves', ?_, ?_, ?_, ?_⟩
      · intro lf' hlf'
        obtain ⟨lf, hlf, hmem⟩ := List.mem_flatMap.mp hlf'
        have hc := hc_le lf hlf
        rw [hcnt_snoc, hpaid]
        simp only [splitFun, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hmem
        rcases hmem with rfl | rfl <;> dsimp [mkChild] <;> omega
      · intro y hy

        have hfp := list_flatMap_partition leaves splitFun
          (fun lf (yp : {y : Fin k → F // y ∈ AffSet eqs0}) => yp.1 ∈ AffSet lf.eqs)
          (fun lf' (yp : {y : Fin k → F // y ∈ AffSet eqs0}) => yp.1 ∈ AffSet lf'.eqs)
          (fun yp => hpart yp.1 yp.2)
          (fun lf _ yp hyp => by
            let γ : F := (∑ i : Fin k, (lf.lin fa).1 i * yp.1 i) + (lf.lin fa).2
            rcases zmod2_cases γ with hγ0 | hγ1
            · refine ⟨⟨0, by simp [splitFun]⟩, ?_, ?_⟩
              · exact (hchild_mem lf 0 yp.1).mpr ⟨hyp, hγ0⟩
              · intro j hj
                have hjlt : j.val < 2 := by simpa [splitFun] using j.isLt
                rcases (show j.val = 0 ∨ j.val = 1 by omega) with h0 | h1
                · exact Fin.ext h0
                · exfalso
                  have hj1 : (splitFun lf).get j = mkChild lf 1 := by
                    simp [splitFun, List.get_eq_getElem, h1]
                  rw [hj1] at hj
                  have := ((hchild_mem lf 1 yp.1).mp hj).2
                  dsimp [γ] at hγ0; rw [hγ0] at this; exact zero_ne_one this
            · refine ⟨⟨1, by simp [splitFun]⟩, ?_, ?_⟩
              · exact (hchild_mem lf 1 yp.1).mpr ⟨hyp, hγ1⟩
              · intro j hj
                have hjlt : j.val < 2 := by simpa [splitFun] using j.isLt
                rcases (show j.val = 0 ∨ j.val = 1 by omega) with h0 | h1
                · exfalso
                  have hj0 : (splitFun lf).get j = mkChild lf 0 := by
                    simp [splitFun, List.get_eq_getElem, h0]
                  rw [hj0] at hj
                  have := ((hchild_mem lf 0 yp.1).mp hj).2
                  dsimp [γ] at hγ1; rw [hγ1] at this; exact one_ne_zero this
                · exact Fin.ext h1)
          (fun lf _ lf' hmem yp hyp => by
            simp only [splitFun, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hmem
            rcases hmem with rfl | rfl
            · exact ((hchild_mem lf 0 yp.1).mp hyp).1
            · exact ((hchild_mem lf 1 yp.1).mp hyp).1)
          ⟨y, hy⟩
        exact hfp
      · intro lf' hlf' y hy
        obtain ⟨lf, hlf, hmem⟩ := List.mem_flatMap.mp hlf'
        simp only [splitFun, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hmem
        rcases hmem with rfl | rfl
        · exact hsub lf hlf y ((hchild_mem lf 0 y).mp hy).1
        · exact hsub lf hlf y ((hchild_mem lf 1 y).mp hy).1
      · intro lf' hlf' y hy w
        obtain ⟨lf, hlf, hmem⟩ := List.mem_flatMap.mp hlf'
        simp only [splitFun, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hmem
        have hcheck : ∀ γ : F, y ∈ AffSet (mkChild lf γ).eqs →
            b2z ((wireList (gs ++ [g]) (bitsVec k y)).getD w.val false) =
              (∑ i : Fin k, ((mkChild lf γ).lin w).1 i * y i) + ((mkChild lf γ).lin w).2 := by
          intro γ hγmem
          have hch := (hchild_mem lf γ y).mp hγmem
          by_cases hw : w.val < k + gs.length
          · dsimp [mkChild]; rw [dif_pos hw]
            have := hwire_pre y ⟨w.val, hw⟩
            dsimp at this; rw [this]
            exact hsem lf hlf y hch.1 ⟨w.val, hw⟩
          · dsimp [mkChild]; rw [dif_neg hw, hfin_last w hw, hwire_last, hgab]
            have hwa : b2z ((wireList gs (bitsVec k y)).getD a false) = γ := by
              have := hsem lf hlf y hch.1 fa
              dsimp [fa] at this; rw [this, hch.2]
            have hwb : b2z ((wireList gs (bitsVec k y)).getD b false) =
                (∑ i : Fin k, (lf.lin fb).1 i * y i) + (lf.lin fb).2 :=
              hsem lf hlf y hch.1 fb
            rcases hop_ab with hop | hop
            · rw [hop]
              simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id,
                Bool.and_true, b2z_and, hwa, hwb, ↓reduceIte]
              rcases zmod2_cases γ with rfl | rfl <;> simp
            · rw [hop]
              have hor : ¬ (GateOp.or = GateOp.and) := by intro h; cases h
              simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id,
                Bool.or_false, b2z_or, hwa, hwb, hor, ↓reduceIte]
              rcases zmod2_cases γ with rfl | rfl
              · simp
              · simp only [one_ne_zero, ↓reduceIte, zero_mul, Finset.sum_const_zero, zero_add]
                ring_nf
                rw [show (2 : F) = 0 by decide]; ring
        rcases hmem with rfl | rfl
        · exact hcheck 0 hy
        · exact hcheck 1 hy

structure DualBasis (k : ℕ) where
  α : Fin k → Fin k → F
  u : Fin k → Fin k → F
  biorth : ∀ i j : Fin k, dotProduct (α i) (u j) = if i = j then 1 else 0

def stdDualBasis (k : ℕ) : DualBasis k where
  α := fun i j => if i = j then 1 else 0
  u := fun i j => if i = j then 1 else 0
  biorth := fun i j => by
    simp only [dotProduct]
    rw [Finset.sum_eq_single i]
    · by_cases h : i = j
      · subst h; simp
      · simp [h, Ne.symm h]
    · intro r _ hri; simp [Ne.symm hri]
    · intro h; exact absurd (Finset.mem_univ i) h

lemma DualBasis.expand_u {k : ℕ} (B : DualBasis k) (v : Fin k → F) :
    v = fun p => ∑ i : Fin k, dotProduct (B.α i) v * B.u i p := by
  let T : (Fin k → F) → (Fin k → F) := fun x i => dotProduct (B.α i) x
  let S : (Fin k → F) → (Fin k → F) := fun w p => ∑ j : Fin k, w j * B.u j p
  have hTS : ∀ w, T (S w) = w := by
    intro w; funext i
    dsimp [T, S, dotProduct]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    have h1 : ∀ j : Fin k, (∑ p : Fin k, B.α i p * (w j * B.u j p)) = w j * dotProduct (B.α i) (B.u j) := by
      intro j; dsimp [dotProduct]; rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro p _; ring
    simp_rw [h1, B.biorth]
    simp
  have hTsurj : Function.Surjective T := fun w => ⟨S w, hTS w⟩
  have hTinj : Function.Injective T := Finite.injective_iff_surjective.mpr hTsurj
  exact (hTinj (hTS (T v))).symm

lemma DualBasis.expand_α {k : ℕ} (B : DualBasis k) (v : Fin k → F) :
    v = fun q => ∑ i : Fin k, dotProduct v (B.u i) * B.α i q := by
  let T : (Fin k → F) → (Fin k → F) := fun x j => dotProduct x (B.u j)
  let S : (Fin k → F) → (Fin k → F) := fun w q => ∑ i : Fin k, w i * B.α i q
  have hTS : ∀ w, T (S w) = w := by
    intro w; funext j
    dsimp [T, S, dotProduct]
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    have h1 : ∀ i : Fin k, (∑ q : Fin k, w i * B.α i q * B.u j q) = w i * dotProduct (B.α i) (B.u j) := by
      intro i; dsimp [dotProduct]; rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro q _; ring
    simp_rw [h1, B.biorth]
    simp
  have hTsurj : Function.Surjective T := fun w => ⟨S w, hTS w⟩
  have hTinj : Function.Injective T := Finite.injective_iff_surjective.mpr hTsurj
  exact (hTinj (hTS (T v))).symm

def DualBasis.swap {k : ℕ} (B : DualBasis k) (d0 p : Fin k) : DualBasis k where
  α := fun i => B.α (Equiv.swap d0 p i)
  u := fun j => B.u (Equiv.swap d0 p j)
  biorth := fun i j => by
    rw [B.biorth]
    simp [(Equiv.swap d0 p).injective.eq_iff]

def DualBasis.replaceAt {k : ℕ} (B : DualBasis k) (d0 : Fin k) (β' : Fin k → F)
    (hlow : ∀ j : Fin k, j.val < d0.val → dotProduct β' (B.u j) = 0)
    (hd0 : dotProduct β' (B.u d0) = 1) : DualBasis k where
  α := fun i => if i = d0 then β' else B.α i
  u := fun j => if d0.val < j.val then fun p => B.u j p + dotProduct β' (B.u j) * B.u d0 p else B.u j
  biorth := fun i j => by
    by_cases hi : i = d0
    · subst i
      simp only [↓reduceIte]
      by_cases hj : d0.val < j.val
      · simp only [hj, ↓reduceIte]
        have hne : d0 ≠ j := fun h => by subst h; omega
        rw [if_neg hne]
        have hdot : dotProduct β' (fun p => B.u j p + dotProduct β' (B.u j) * B.u d0 p) =
            dotProduct β' (B.u j) + dotProduct β' (B.u j) * dotProduct β' (B.u d0) := by
          simp only [dotProduct, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
          congr 1; apply Finset.sum_congr rfl; intro p _; ring
        rw [hdot, hd0, mul_one, zmod2_add_self]
      · simp only [hj, ↓reduceIte]
        by_cases heq : d0 = j
        · subst heq; simp [hd0]
        · rw [if_neg heq]
          exact hlow j (by have : j.val ≠ d0.val := fun h => heq (Fin.ext h.symm); omega)
    · simp only [hi, ↓reduceIte]
      by_cases hj : d0.val < j.val
      · simp only [hj, ↓reduceIte]
        have hdot : dotProduct (B.α i) (fun p => B.u j p + dotProduct β' (B.u j) * B.u d0 p) =
            dotProduct (B.α i) (B.u j) + dotProduct β' (B.u j) * dotProduct (B.α i) (B.u d0) := by
          simp only [dotProduct, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
          congr 1; apply Finset.sum_congr rfl; intro p _; ring
        rw [hdot, B.biorth i j, B.biorth i d0, if_neg hi, mul_zero, add_zero]
      · simp only [hj, ↓reduceIte]
        exact B.biorth i j

structure YProg (n : ℕ) where
  gates : List Gate
  rb : ∀ j < gates.length, ∀ idx ∈ (gates.getD j ⟨.or, []⟩).inputs, idx < n + j
  leg : ∀ h ∈ gates, legalGate h

def YProg.empty (n : ℕ) : YProg n where
  gates := []
  rb := fun _ h => by simp at h
  leg := fun _ h => by simp at h

def YProg.valList {n : ℕ} (P : YProg n) (inp : List Bool) (w : ℕ) : F :=
  b2z ((wireList P.gates inp).getD w false)

def YProg.val {n : ℕ} (P : YProg n) (y : Fin n → F) (w : ℕ) : F :=
  P.valList (bitsVec n y) w

def YProg.pushGate {n : ℕ} (P : YProg n) (g : Gate)
    (hrb : ∀ idx ∈ g.inputs, idx < n + P.gates.length) (hleg : legalGate g) : YProg n where
  gates := P.gates ++ [g]
  rb := fun j hj idx hidx => by
    by_cases hlt : j < P.gates.length
    · have hget : (P.gates ++ [g]).getD j ⟨.or, []⟩ = P.gates.getD j ⟨.or, []⟩ := by
        rw [List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ hlt, List.getElem_append_left hlt]
      rw [hget] at hidx
      exact P.rb j hlt idx hidx
    · have heq : j = P.gates.length := by simp at hj; omega
      subst heq
      have hget : (P.gates ++ [g]).getD P.gates.length ⟨.or, []⟩ = g := by
        rw [List.getD_eq_getElem _ _ hj, List.getElem_append_right (Nat.le_refl _)]; simp
      rw [hget] at hidx
      exact hrb idx hidx
  leg := fun h hh => by
    rcases List.mem_append.mp hh with h1 | h2
    · exact P.leg h h1
    · rw [List.mem_singleton.mp h2]; exact hleg

lemma YProg.pushGate_oldList {n : ℕ} (P : YProg n) (g : Gate)
    {hrb : ∀ idx ∈ g.inputs, idx < n + P.gates.length} {hleg : legalGate g}
    (inp : List Bool) (hinp : inp.length = n) {w : ℕ} (hw : w < n + P.gates.length) :
    (P.pushGate g hrb hleg).valList inp w = P.valList inp w := by
  dsimp [YProg.valList, YProg.pushGate]
  rw [wireList_append]
  have hlt : w < (wireList P.gates inp).length := by rw [wireList_length, hinp]; exact hw
  rw [wireList_getD_lt [g] _ w hlt]

lemma YProg.pushGate_old {n : ℕ} (P : YProg n) (g : Gate)
    {hrb : ∀ idx ∈ g.inputs, idx < n + P.gates.length} {hleg : legalGate g}
    (y : Fin n → F) {w : ℕ} (hw : w < n + P.gates.length) :
    (P.pushGate g hrb hleg).val y w = P.val y w :=
  P.pushGate_oldList g (bitsVec n y) (by simp [bitsVec]) hw

lemma YProg.pushGate_lastList {n : ℕ} (P : YProg n) (g : Gate)
    {hrb : ∀ idx ∈ g.inputs, idx < n + P.gates.length} {hleg : legalGate g}
    (inp : List Bool) (hinp : inp.length = n) :
    (P.pushGate g hrb hleg).valList inp (n + P.gates.length) =
      b2z (g.op.eval (g.inputs.map fun idx => (wireList P.gates inp).getD idx false)) := by
  dsimp [YProg.valList, YProg.pushGate]
  congr 1
  simpa [hinp] using wireList_snoc_last P.gates g inp

lemma YProg.pushGate_last {n : ℕ} (P : YProg n) (g : Gate)
    {hrb : ∀ idx ∈ g.inputs, idx < n + P.gates.length} {hleg : legalGate g}
    (y : Fin n → F) :
    (P.pushGate g hrb hleg).val y (n + P.gates.length) =
      b2z (g.op.eval (g.inputs.map fun idx => (wireList P.gates (bitsVec n y)).getD idx false)) :=
  P.pushGate_lastList g (bitsVec n y) (by simp [bitsVec])

lemma YProg.pushGate_cost {n : ℕ} (P : YProg n) (g : Gate)
    {hrb : ∀ idx ∈ g.inputs, idx < n + P.gates.length} {hleg : legalGate g} :
    (P.pushGate g hrb hleg).gates.countP isPaid =
      P.gates.countP isPaid + if isPaid g then 1 else 0 := by
  dsimp [YProg.pushGate]
  rw [List.countP_append, List.countP_singleton]

def YProg.pushConst {n : ℕ} (P : YProg n) (c : F) :
    {Q : YProg n × ℕ //
      P.gates.length ≤ Q.1.gates.length ∧
      Q.2 < n + Q.1.gates.length ∧
      Q.1.gates.countP isPaid = P.gates.countP isPaid ∧
      (∀ inp, inp.length = n → ∀ w < n + P.gates.length, Q.1.valList inp w = P.valList inp w) ∧
      (∀ inp, inp.length = n → Q.1.valList inp Q.2 = c)} :=
  let g : Gate := if c = 0 then ⟨.or, []⟩ else ⟨.and, []⟩
  let hrb : ∀ idx ∈ g.inputs, idx < n + P.gates.length := by
    intro idx h; dsimp [g] at h; split_ifs at h <;> simp at h
  let hleg : legalGate g := by dsimp [g]; split_ifs <;> simp [legalGate]
  let P1 := P.pushGate g hrb hleg
  ⟨(P1, n + P.gates.length), by
    refine ⟨by simp [P1, YProg.pushGate], by simp [P1, YProg.pushGate], ?_,
      fun inp hinp w hw => by dsimp [P1]; exact P.pushGate_oldList g inp hinp hw, fun inp hinp => ?_⟩
    · dsimp [P1]; rw [P.pushGate_cost]; rcases zmod2_cases c with rfl | rfl <;> simp [g, isPaid]
    · dsimp [P1]; rw [P.pushGate_lastList g inp hinp]; rcases zmod2_cases c with rfl | rfl <;> simp [g, GateOp.eval, b2z]⟩

def YProg.pushNot {n : ℕ} (P : YProg n) (a : ℕ) (ha : a < n + P.gates.length) :
    {Q : YProg n × ℕ //
      P.gates.length ≤ Q.1.gates.length ∧
      Q.2 < n + Q.1.gates.length ∧
      Q.1.gates.countP isPaid = P.gates.countP isPaid ∧
      (∀ inp, inp.length = n → ∀ w < n + P.gates.length, Q.1.valList inp w = P.valList inp w) ∧
      (∀ inp, inp.length = n → Q.1.valList inp Q.2 = P.valList inp a + 1)} :=
  let g : Gate := ⟨.not, [a]⟩
  let hrb : ∀ idx ∈ g.inputs, idx < n + P.gates.length := by intro idx h; simp [g] at h; subst h; exact ha
  let hleg : legalGate g := by simp [g, legalGate]
  let P1 := P.pushGate g hrb hleg
  ⟨(P1, n + P.gates.length), by
    refine ⟨by simp [P1, YProg.pushGate], by simp [P1, YProg.pushGate], ?_,
      fun inp hinp w hw => by dsimp [P1]; exact P.pushGate_oldList g inp hinp hw, fun inp hinp => ?_⟩
    · dsimp [P1]; rw [P.pushGate_cost]; simp [g, isPaid]
    · dsimp [P1]; rw [P.pushGate_lastList g inp hinp]; simp [g, GateOp.eval, b2z_not, YProg.valList]⟩

def YProg.pushXor {n : ℕ} (P : YProg n) (a b : ℕ)
    (ha : a < n + P.gates.length) (hb : b < n + P.gates.length) :
    {Q : YProg n × ℕ //
      P.gates.length ≤ Q.1.gates.length ∧
      Q.2 < n + Q.1.gates.length ∧
      Q.1.gates.countP isPaid = P.gates.countP isPaid ∧
      (∀ inp, inp.length = n → ∀ w < n + P.gates.length, Q.1.valList inp w = P.valList inp w) ∧
      (∀ inp, inp.length = n → Q.1.valList inp Q.2 = P.valList inp a + P.valList inp b)} :=
  let g1 : Gate := ⟨.mod 2, [a, b]⟩
  let hrb1 : ∀ idx ∈ g1.inputs, idx < n + P.gates.length := by
    intro idx h; simp [g1] at h; rcases h with rfl | rfl <;> assumption
  let hleg1 : legalGate g1 := by simp [g1, legalGate]
  let P1 := P.pushGate g1 hrb1 hleg1
  let w1 := n + P.gates.length
  let hw1 : w1 < n + P1.gates.length := by simp [P1, YProg.pushGate, w1]
  let r2 := P1.pushNot w1 hw1
  ⟨r2.val, by
    refine ⟨le_trans (by simp [P1, YProg.pushGate]) r2.property.1, r2.property.2.1, ?_, ?_, ?_⟩
    · rw [r2.property.2.2.1]; dsimp [P1]; rw [P.pushGate_cost]; simp [g1, isPaid]
    · intro inp hinp w hw
      rw [r2.property.2.2.2.1 inp hinp w (by simp [P1, YProg.pushGate]; omega)]
      exact P.pushGate_oldList g1 inp hinp hw
    · intro inp hinp
      rw [r2.property.2.2.2.2 inp hinp]
      dsimp [P1, w1]
      rw [P.pushGate_lastList g1 inp hinp]
      simp only [g1, List.map_cons, List.map_nil, b2z_mod2_pair, YProg.valList]
      rw [add_assoc, zmod2_add_self, add_zero]⟩

def YProg.pushPaid {n : ℕ} (P : YProg n) (op : GateOp) (hop : op = .and ∨ op = .or)
    (a b : ℕ) (ha : a < n + P.gates.length) (hb : b < n + P.gates.length) :
    {Q : YProg n × ℕ //
      P.gates.length ≤ Q.1.gates.length ∧
      Q.2 < n + Q.1.gates.length ∧
      Q.1.gates.countP isPaid = P.gates.countP isPaid + 1 ∧
      (∀ inp, inp.length = n → ∀ w < n + P.gates.length, Q.1.valList inp w = P.valList inp w) ∧
      (∀ inp, inp.length = n → Q.1.valList inp Q.2 =
        if op = .and then P.valList inp a * P.valList inp b
        else P.valList inp a + P.valList inp b + P.valList inp a * P.valList inp b)} :=
  let g : Gate := ⟨op, [a, b]⟩
  let hrb : ∀ idx ∈ g.inputs, idx < n + P.gates.length := by
    intro idx h; simp [g] at h; rcases h with rfl | rfl <;> assumption
  let hleg : legalGate g := by refine ⟨by simp [g], ?_⟩; rcases hop with rfl | rfl <;> simp [g]
  let P1 := P.pushGate g hrb hleg
  ⟨(P1, n + P.gates.length), by
    refine ⟨by simp [P1, YProg.pushGate], by simp [P1, YProg.pushGate], ?_,
      fun inp hinp w hw => by dsimp [P1]; exact P.pushGate_oldList g inp hinp hw, fun inp hinp => ?_⟩
    · dsimp [P1]; rw [P.pushGate_cost]; rcases hop with rfl | rfl <;> simp [g, isPaid]
    · dsimp [P1]; rw [P.pushGate_lastList g inp hinp]
      rcases hop with rfl | rfl
      · simp [g, GateOp.eval, b2z_and, YProg.valList]
      · simp [g, GateOp.eval, b2z_or, YProg.valList]⟩

def YProg.pushLinComb {n : ℕ} (P : YProg n) :
    ∀ (l : List (F × ℕ)), (∀ p ∈ l, p.2 < n + P.gates.length) →
      {Q : YProg n × ℕ //
        P.gates.length ≤ Q.1.gates.length ∧
        Q.2 < n + Q.1.gates.length ∧
        Q.1.gates.countP isPaid = P.gates.countP isPaid ∧
        (∀ y w, w < n + P.gates.length → Q.1.val y w = P.val y w) ∧
        (∀ y, Q.1.val y Q.2 = (l.map fun p => p.1 * P.val y p.2).sum)}
  | [], _ =>
    let r := P.pushConst 0
    ⟨r.val, r.property.1, r.property.2.1, r.property.2.2.1,
      fun y w hw => r.property.2.2.2.1 (bitsVec n y) (by simp [bitsVec]) w hw,
      fun y => by simp only [YProg.val, List.map_nil, List.sum_nil]; exact r.property.2.2.2.2 (bitsVec n y) (by simp [bitsVec])⟩
  | (c, w) :: rest, hmem =>
    let rRest := P.pushLinComb rest (fun p hp => hmem p (List.mem_cons_of_mem _ hp))
    if hc : c = 0 then
      ⟨rRest.val, rRest.property.1, rRest.property.2.1, rRest.property.2.2.1,
        rRest.property.2.2.2.1, fun y => by simp [hc, rRest.property.2.2.2.2]⟩
    else
      have hw1 : w < n + rRest.val.1.gates.length := by
        have hw0 := hmem (c, w) (List.mem_cons_self ..)
        have hle := rRest.property.1; omega
      let rAdd := rRest.val.1.pushXor w rRest.val.2 hw1 rRest.property.2.1
      ⟨rAdd.val,
        le_trans rRest.property.1 rAdd.property.1,
        rAdd.property.2.1,
        by rw [rAdd.property.2.2.1, rRest.property.2.2.1],
        fun y u hu => by
          rw [YProg.val, rAdd.property.2.2.2.1 (bitsVec n y) (by simp [bitsVec]) u (by have := rRest.property.1; omega)]
          exact rRest.property.2.2.2.1 y u hu,
        fun y => by
          rw [YProg.val, rAdd.property.2.2.2.2 (bitsVec n y) (by simp [bitsVec])]
          change rRest.val.1.val y w + rRest.val.1.val y rRest.val.2 = _
          rw [rRest.property.2.2.2.1 y w (hmem (c, w) (List.mem_cons_self ..)),
            rRest.property.2.2.2.2 y]
          have hc1 : c = 1 := zmod2_eq_one_of_ne_zero hc
          simp [hc1]⟩

def YProg.pushSumFin {n : ℕ} (P : YProg n) (d : ℕ) (c : Fin d → F) (rw : Fin d → ℕ)
    (hrw : ∀ t : Fin d, rw t < n + P.gates.length) :
    {Q : YProg n × ℕ //
      P.gates.length ≤ Q.1.gates.length ∧
      Q.2 < n + Q.1.gates.length ∧
      Q.1.gates.countP isPaid = P.gates.countP isPaid ∧
      (∀ y w, w < n + P.gates.length → Q.1.val y w = P.val y w) ∧
      (∀ y, Q.1.val y Q.2 = ∑ t : Fin d, c t * P.val y (rw t))} :=
  let l := (List.finRange d).map fun t => (c t, rw t)
  let r := P.pushLinComb l (by
    intro p hp; obtain ⟨t, _, rfl⟩ := List.mem_map.mp hp; exact hrw t)
  ⟨r.val, r.property.1, r.property.2.1, r.property.2.2.1, r.property.2.2.2.1, fun y => by
    rw [r.property.2.2.2.2 y]
    dsimp [l]
    rw [List.map_map, ← Fin.sum_univ_def]
    rfl⟩

structure RowLeaf (k nw : ℕ) where
  d : ℕ
  hd : d ≤ k
  B : DualBasis k
  prog : YProg k
  rw : Fin d → ℕ
  hrw : ∀ t : Fin d, rw t < k + prog.gates.length
  beta : Fin nw → (Fin k → F)
  yw : Fin nw → ℕ
  hyw : ∀ w : Fin nw, yw w < k + prog.gates.length

def RowLeaf.InLeaf {k nw : ℕ} (L : RowLeaf k nw) (x y : Fin k → F) : Prop :=
  ∀ t : Fin L.d, dotProduct (L.B.α ⟨t.val, lt_of_lt_of_le t.isLt L.hd⟩) x = L.prog.val y (L.rw t)

lemma row_leaf_partition (k : ℕ) :
    ∀ (gs : List Gate),
      (∀ j < gs.length, ∀ idx ∈ (gs.getD j ⟨.or, []⟩).inputs, idx < 2 * k + j) →
      (∀ h ∈ gs, legalGate h) →
      ∃ leaves : List (RowLeaf k (2 * k + gs.length)),
        (∀ L ∈ leaves, L.d + L.prog.gates.countP isPaid ≤ gs.countP isPaid) ∧
        (∀ x y : Fin k → F, ∃! idx : Fin leaves.length, (leaves.get idx).InLeaf x y) ∧
        (∀ L ∈ leaves, ∀ x y : Fin k → F, L.InLeaf x y →
          ∀ w : Fin (2 * k + gs.length),
            b2z ((wireList gs (bitsVec k x ++ bitsVec k y)).getD w.val false) =
              dotProduct (L.beta w) x + L.prog.val y (L.yw w)) := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil =>
    intro _ _
    simp only [List.countP_nil, List.length_nil, add_zero]
    let r0 := (YProg.empty k).pushConst 0
    let L0 : RowLeaf k (2 * k) :=
      { d := 0
        hd := Nat.zero_le k
        B := stdDualBasis k
        prog := r0.val.1
        rw := Fin.elim0
        hrw := fun t => Fin.elim0 t
        beta := fun w =>
          if hw : w.val < k then (fun j => if j = ⟨w.val, hw⟩ then 1 else 0) else (fun _ => 0)
        yw := fun w => if w.val < k then r0.val.2 else w.val - k
        hyw := fun w => by
          split_ifs with hw
          · exact r0.property.2.1
          · have := w.isLt; have := r0.property.1; omega }
    refine ⟨[L0], ?_, ?_, ?_⟩
    · intro L hL
      rw [List.mem_singleton.mp hL]
      dsimp [L0]
      rw [r0.property.2.2.1]
      simp [YProg.empty]
    · intro x y
      refine ⟨⟨0, by simp⟩, fun t => Fin.elim0 t, fun idx _ => Fin.ext (by have := idx.isLt; simp at this ⊢)⟩
    · intro L hL x y _ w
      rw [List.mem_singleton.mp hL]
      dsimp [L0, wireList]
      have hlenx : (bitsVec k x).length = k := by simp [bitsVec]
      have hleny : (bitsVec k y).length = k := by simp [bitsVec]
      by_cases hw : w.val < k
      · simp only [hw, ↓reduceDIte, ↓reduceIte]
        rw [getD_append_lt (by rw [hlenx]; exact hw)]
        have hr0 : r0.val.1.val y r0.val.2 = 0 :=
          r0.property.2.2.2.2 (bitsVec k y) (by simp [bitsVec])
        dsimp [bitsVec]
        rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn, b2z_decide_eq_one,
          hr0, add_zero]
        simp [dotProduct]
      · simp only [hw, ↓reduceDIte, ↓reduceIte]
        have hw' : w.val < (bitsVec k x ++ bitsVec k y).length := by simp [hlenx, hleny]; omega
        rw [List.getD_eq_getElem _ _ hw', List.getElem_append_right (by rw [hlenx]; omega)]
        have hlt_y : w.val - k < (bitsVec k y).length := by rw [hleny]; omega
        have helem : (bitsVec k y)[w.val - k]'hlt_y = decide (y ⟨w.val - k, by omega⟩ = 1) := by
          simp [bitsVec]
        simp only [hlenx, helem, b2z_decide_eq_one]
        have h0 : dotProduct (fun _ : Fin k => (0 : F)) x = 0 := by simp [dotProduct]
        rw [h0, zero_add]
        have hlt : w.val - k < k + (YProg.empty k).gates.length := by
          simp [YProg.empty]; omega
        have hold := r0.property.2.2.2.1 (bitsVec k y) (by simp [bitsVec]) (w.val - k) hlt
        change _ = r0.val.1.valList (bitsVec k y) (w.val - k)
        rw [hold]
        dsimp [YProg.valList, YProg.empty, wireList, bitsVec]
        rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn, b2z_decide_eq_one]
  | append_singleton gs g ih =>
    intro hrb hleg
    have hrb_pre : ∀ j < gs.length, ∀ idx ∈ (gs.getD j ⟨.or, []⟩).inputs, idx < 2 * k + j := by
      intro j hj idx hidx
      have h1 := hrb j (by simp; omega) idx
      have hget : (gs ++ [g]).getD j ⟨.or, []⟩ = gs.getD j ⟨.or, []⟩ := by
        rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ hj,
          List.getElem_append_left hj]
      rw [hget] at h1
      exact h1 hidx
    have hrb_last : ∀ idx ∈ g.inputs, idx < 2 * k + gs.length := by
      intro idx hidx
      have h1 := hrb gs.length (by simp) idx
      have hget : (gs ++ [g]).getD gs.length ⟨.or, []⟩ = g := by
        rw [List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (Nat.le_refl _)]
        simp
      rw [hget] at h1
      exact h1 hidx
    have hleg_pre : ∀ h ∈ gs, legalGate h := fun h hh => hleg h (List.mem_append_left _ hh)
    have hleg_g : legalGate g := hleg g (List.mem_append_right _ (List.mem_singleton_self _))
    obtain ⟨leaves, hcost, hpart, hsem⟩ := ih hrb_pre hleg_pre
    have hlen_snoc : (gs ++ [g]).length = gs.length + 1 := by simp
    have hcnt_snoc : (gs ++ [g]).countP isPaid = gs.countP isPaid + if isPaid g then 1 else 0 := by
      rw [List.countP_append, List.countP_singleton]
    have hwire_pre : ∀ x y (w : Fin (2 * k + gs.length)),
        (wireList (gs ++ [g]) (bitsVec k x ++ bitsVec k y)).getD w.val false =
        (wireList gs (bitsVec k x ++ bitsVec k y)).getD w.val false := by
      intro x y w
      rw [wireList_append]
      have hlt : w.val < (wireList gs (bitsVec k x ++ bitsVec k y)).length := by
        rw [wireList_length, List.length_append, bitsVec, bitsVec, List.length_ofFn, List.length_ofFn]
        have := w.isLt; omega
      exact wireList_getD_lt [g] _ w.val hlt
    have hwire_last : ∀ x y,
        (wireList (gs ++ [g]) (bitsVec k x ++ bitsVec k y)).getD (2 * k + gs.length) false =
        g.op.eval (g.inputs.map fun idx => (wireList gs (bitsVec k x ++ bitsVec k y)).getD idx false) := by
      intro x y
      have hbl : (bitsVec k x ++ bitsVec k y).length = 2 * k := by simp [bitsVec]; omega
      simpa [hbl] using wireList_snoc_last gs g (bitsVec k x ++ bitsVec k y)
    have hfin_last : ∀ w : Fin (2 * k + (gs ++ [g]).length), ¬ w.val < 2 * k + gs.length → w.val = 2 * k + gs.length := by
      intro w hw
      have hlt : w.val < 2 * k + (gs.length + 1) := by simpa [hlen_snoc] using w.isLt
      omega
    have hexpand : ∀ (L : RowLeaf k (2 * k + gs.length)),
        L.d + L.prog.gates.countP isPaid ≤ gs.countP isPaid →
        (∀ x y : Fin k → F, L.InLeaf x y → ∀ w : Fin (2 * k + gs.length),
          b2z ((wireList gs (bitsVec k x ++ bitsVec k y)).getD w.val false) =
            dotProduct (L.beta w) x + L.prog.val y (L.yw w)) →
        ∃ children : List (RowLeaf k (2 * k + (gs ++ [g]).length)),
          (∀ L' ∈ children, L'.d + L'.prog.gates.countP isPaid ≤ (gs ++ [g]).countP isPaid) ∧
          (∀ x y : Fin k → F, L.InLeaf x y →
            ∃! idx : Fin children.length, (children.get idx).InLeaf x y) ∧
          (∀ L' ∈ children, ∀ x y : Fin k → F, L'.InLeaf x y → L.InLeaf x y) ∧
          (∀ L' ∈ children, ∀ x y : Fin k → F, L'.InLeaf x y →
            ∀ w : Fin (2 * k + (gs ++ [g]).length),
              b2z ((wireList (gs ++ [g]) (bitsVec k x ++ bitsVec k y)).getD w.val false) =
                dotProduct (L'.beta w) x + L'.prog.val y (L'.yw w)) := by
      intro L hLcost hLsem
      cases hpaid : isPaid g
      ·
        have hext : ∃ (P1 : YProg k) (βn : Fin k → F) (wn : ℕ),
            L.prog.gates.length ≤ P1.gates.length ∧
            wn < k + P1.gates.length ∧
            P1.gates.countP isPaid = L.prog.gates.countP isPaid ∧
            (∀ y w, w < k + L.prog.gates.length → P1.val y w = L.prog.val y w) ∧
            (∀ x y, L.InLeaf x y →
              b2z ((wireList (gs ++ [g]) (bitsVec k x ++ bitsVec k y)).getD (2 * k + gs.length) false) =
                dotProduct βn x + P1.val y wn) := by
          match hg_in : g.inputs with
          | [] =>
            let r := L.prog.pushConst (b2z (g.op.eval []))
            refine ⟨r.val.1, fun _ => 0, r.val.2, r.property.1, r.property.2.1,
              r.property.2.2.1,
              fun y w hw => r.property.2.2.2.1 (bitsVec k y) (by simp [bitsVec]) w hw,
              fun x y _ => ?_⟩
            rw [hwire_last, hg_in]
            have hr := r.property.2.2.2.2 (bitsVec k y) (by simp [bitsVec])
            change _ = dotProduct (fun _ => 0) x + r.val.1.valList (bitsVec k y) r.val.2
            rw [hr]; simp [dotProduct]
          | [a] =>
            have ha : a < 2 * k + gs.length := hrb_last a (by simp [hg_in])
            let fa : Fin (2 * k + gs.length) := ⟨a, ha⟩
            rcases hleg_g.2 with hop | hop | hop | ⟨hop, _⟩
            · refine ⟨L.prog, L.beta fa, L.yw fa, le_refl _, L.hyw fa, rfl, fun _ _ _ => rfl, fun x y hxy => ?_⟩
              rw [hwire_last, hg_in, hop]
              simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id, Bool.and_true]
              exact hLsem x y hxy fa
            · refine ⟨L.prog, L.beta fa, L.yw fa, le_refl _, L.hyw fa, rfl, fun _ _ _ => rfl, fun x y hxy => ?_⟩
              rw [hwire_last, hg_in, hop]
              simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id, Bool.or_false]
              exact hLsem x y hxy fa
            · let r := L.prog.pushNot (L.yw fa) (L.hyw fa)
              refine ⟨r.val.1, L.beta fa, r.val.2, r.property.1, r.property.2.1,
                r.property.2.2.1,
                fun y w hw => r.property.2.2.2.1 (bitsVec k y) (by simp [bitsVec]) w hw,
                fun x y hxy => ?_⟩
              rw [hwire_last, hg_in, hop]
              simp only [List.map_cons, List.map_nil, b2z_mod2_single]
              have hr := r.property.2.2.2.2 (bitsVec k y) (by simp [bitsVec])
              change _ = dotProduct (L.beta fa) x + r.val.1.valList (bitsVec k y) r.val.2
              rw [hLsem x y hxy fa, hr]; dsimp [YProg.val, YProg.valList]; ring
            · let r := L.prog.pushNot (L.yw fa) (L.hyw fa)
              refine ⟨r.val.1, L.beta fa, r.val.2, r.property.1, r.property.2.1,
                r.property.2.2.1,
                fun y w hw => r.property.2.2.2.1 (bitsVec k y) (by simp [bitsVec]) w hw,
                fun x y hxy => ?_⟩
              rw [hwire_last, hg_in, hop]
              simp only [List.map_cons, List.map_nil, GateOp.eval, List.headD_cons, b2z_not]
              have hr := r.property.2.2.2.2 (bitsVec k y) (by simp [bitsVec])
              change _ = dotProduct (L.beta fa) x + r.val.1.valList (bitsVec k y) r.val.2
              rw [hLsem x y hxy fa, hr]; dsimp [YProg.val, YProg.valList]; ring
          | [a, b] =>
            have ha : a < 2 * k + gs.length := hrb_last a (by simp [hg_in])
            have hb : b < 2 * k + gs.length := hrb_last b (by simp [hg_in])
            let fa : Fin (2 * k + gs.length) := ⟨a, ha⟩
            let fb : Fin (2 * k + gs.length) := ⟨b, hb⟩
            rcases hleg_g.2 with hop | hop | hop | ⟨_, h1⟩
            · exfalso; simp [isPaid, hg_in, hop] at hpaid
            · exfalso; simp [isPaid, hg_in, hop] at hpaid
            · let r1 := L.prog.pushXor (L.yw fa) (L.yw fb) (L.hyw fa) (L.hyw fb)
              let r2 := r1.val.1.pushNot r1.val.2 r1.property.2.1
              refine ⟨r2.val.1, fun j => L.beta fa j + L.beta fb j, r2.val.2,
                le_trans r1.property.1 r2.property.1, r2.property.2.1,
                by rw [r2.property.2.2.1, r1.property.2.2.1],
                fun y u hu => by
                  change r2.val.1.valList (bitsVec k y) u = L.prog.valList (bitsVec k y) u
                  rw [r2.property.2.2.2.1 (bitsVec k y) (by simp [bitsVec]) u (by have := r1.property.1; omega)]
                  exact r1.property.2.2.2.1 (bitsVec k y) (by simp [bitsVec]) u hu,
                fun x y hxy => ?_⟩
              rw [hwire_last, hg_in, hop]
              simp only [List.map_cons, List.map_nil, b2z_mod2_pair]
              have hr2 := r2.property.2.2.2.2 (bitsVec k y) (by simp [bitsVec])
              have hr1 := r1.property.2.2.2.2 (bitsVec k y) (by simp [bitsVec])
              change _ = dotProduct (fun j => L.beta fa j + L.beta fb j) x + r2.val.1.valList (bitsVec k y) r2.val.2
              rw [hLsem x y hxy fa, hLsem x y hxy fb, hr2, hr1]
              dsimp [YProg.val, YProg.valList]
              simp only [dotProduct, add_mul, Finset.sum_add_distrib]; ring
            · simp [hg_in] at h1
          | _ :: _ :: _ :: _ =>
            have := hleg_g.1; simp [hg_in] at this
        obtain ⟨P1, βn, wn, hle1, hwn, hcost1, hold1, hsem1⟩ := hext
        let L1 : RowLeaf k (2 * k + (gs ++ [g]).length) :=
          { d := L.d
            hd := L.hd
            B := L.B
            prog := P1
            rw := L.rw
            hrw := fun t => by have := L.hrw t; omega
            beta := fun w => if hw : w.val < 2 * k + gs.length then L.beta ⟨w.val, hw⟩ else βn
            yw := fun w => if hw : w.val < 2 * k + gs.length then L.yw ⟨w.val, hw⟩ else wn
            hyw := fun w => by
              by_cases hw : w.val < 2 * k + gs.length
              · rw [dif_pos hw]; have := L.hyw ⟨w.val, hw⟩; omega
              · rw [dif_neg hw]; exact hwn }
        have hIn_iff : ∀ x y, L1.InLeaf x y ↔ L.InLeaf x y := by
          intro x y
          simp only [RowLeaf.InLeaf, L1]
          apply forall_congr'; intro t
          rw [hold1 y (L.rw t) (L.hrw t)]
        refine ⟨[L1], ?_, ?_, ?_, ?_⟩
        · intro L' hL'
          rw [List.mem_singleton.mp hL']
          dsimp [L1]
          rw [hcost1, hcnt_snoc, hpaid]; simp; exact hLcost
        · intro x y hxy
          refine ⟨⟨0, by simp⟩, (hIn_iff x y).mpr hxy, fun idx _ => Fin.ext (by have := idx.isLt; simp at this ⊢)⟩
        · intro L' hL' x y hxy
          rw [List.mem_singleton.mp hL'] at hxy
          exact (hIn_iff x y).mp hxy
        · intro L' hL' x y hxy w
          rw [List.mem_singleton.mp hL'] at hxy ⊢
          have hxy0 := (hIn_iff x y).mp hxy
          dsimp [L1]
          by_cases hw : w.val < 2 * k + gs.length
          · rw [dif_pos hw, dif_pos hw]
            have := hwire_pre x y ⟨w.val, hw⟩
            dsimp at this
            rw [this, hold1 y (L.yw ⟨w.val, hw⟩) (L.hyw ⟨w.val, hw⟩)]
            exact hLsem x y hxy0 ⟨w.val, hw⟩
          · rw [dif_neg hw, dif_neg hw, hfin_last w hw]
            exact hsem1 x y hxy0
      ·
        obtain ⟨a, b, hgab, hop_ab⟩ := gate_eval_paid hpaid
        have ha : a < 2 * k + gs.length := hrb_last a (by simp [hgab])
        have hb : b < 2 * k + gs.length := hrb_last b (by simp [hgab])
        let fa : Fin (2 * k + gs.length) := ⟨a, ha⟩
        let fb : Fin (2 * k + gs.length) := ⟨b, hb⟩
        have hgeval : ∀ x y,
            b2z ((wireList (gs ++ [g]) (bitsVec k x ++ bitsVec k y)).getD (2 * k + gs.length) false) =
              if g.op = .and then
                b2z ((wireList gs (bitsVec k x ++ bitsVec k y)).getD a false) *
                b2z ((wireList gs (bitsVec k x ++ bitsVec k y)).getD b false)
              else
                b2z ((wireList gs (bitsVec k x ++ bitsVec k y)).getD a false) +
                b2z ((wireList gs (bitsVec k x ++ bitsVec k y)).getD b false) +
                b2z ((wireList gs (bitsVec k x ++ bitsVec k y)).getD a false) *
                b2z ((wireList gs (bitsVec k x ++ bitsVec k y)).getD b false) := by
          intro x y
          rw [hwire_last, hgab]
          rcases hop_ab with hop | hop
          · rw [hop]; simp [GateOp.eval, b2z_and]
          · rw [hop]; simp [GateOp.eval, b2z_or]

        have hbranch_on : ∀ (f1 f2 : Fin (2 * k + gs.length)),
            (∀ x y,
              b2z ((wireList (gs ++ [g]) (bitsVec k x ++ bitsVec k y)).getD (2 * k + gs.length) false) =
                if g.op = .and then
                  b2z ((wireList gs (bitsVec k x ++ bitsVec k y)).getD f1.val false) *
                  b2z ((wireList gs (bitsVec k x ++ bitsVec k y)).getD f2.val false)
                else
                  b2z ((wireList gs (bitsVec k x ++ bitsVec k y)).getD f1.val false) +
                  b2z ((wireList gs (bitsVec k x ++ bitsVec k y)).getD f2.val false) +
                  b2z ((wireList gs (bitsVec k x ++ bitsVec k y)).getD f1.val false) *
                  b2z ((wireList gs (bitsVec k x ++ bitsVec k y)).getD f2.val false)) →
            (∃ p : Fin k, L.d ≤ p.val ∧ dotProduct (L.beta f1) (L.B.u p) ≠ 0) →
            ∃ children : List (RowLeaf k (2 * k + (gs ++ [g]).length)),
              (∀ L' ∈ children, L'.d + L'.prog.gates.countP isPaid ≤ (gs ++ [g]).countP isPaid) ∧
              (∀ x y : Fin k → F, L.InLeaf x y →
                ∃! idx : Fin children.length, (children.get idx).InLeaf x y) ∧
              (∀ L' ∈ children, ∀ x y : Fin k → F, L'.InLeaf x y → L.InLeaf x y) ∧
              (∀ L' ∈ children, ∀ x y : Fin k → F, L'.InLeaf x y →
                ∀ w : Fin (2 * k + (gs ++ [g]).length),
                  b2z ((wireList (gs ++ [g]) (bitsVec k x ++ bitsVec k y)).getD w.val false) =
                    dotProduct (L'.beta w) x + L'.prog.val y (L'.yw w)) := by
          intro f1 f2 hsym ⟨p, hpge, hpne⟩
          have hd_lt : L.d < k := lt_of_le_of_lt hpge p.isLt
          let d0 : Fin k := ⟨L.d, hd_lt⟩
          let β1 : Fin k → F := L.beta f1
          let coeff : Fin L.d → F := fun t => dotProduct β1 (L.B.u ⟨t.val, lt_of_lt_of_le t.isLt L.hd⟩)
          let β' : Fin k → F := fun q =>
            β1 q + ∑ t : Fin L.d, coeff t * L.B.α ⟨t.val, lt_of_lt_of_le t.isLt L.hd⟩ q
          have hdot_β' : ∀ j : Fin k,
              dotProduct β' (L.B.u j) =
                if j.val < L.d then 0 else dotProduct β1 (L.B.u j) := by
            intro j
            have hlin : dotProduct β' (L.B.u j) =
                dotProduct β1 (L.B.u j) +
                ∑ t : Fin L.d, coeff t * dotProduct (L.B.α ⟨t.val, lt_of_lt_of_le t.isLt L.hd⟩) (L.B.u j) := by
              simp only [dotProduct, β', add_mul, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
              congr 1; rw [Finset.sum_comm]
              apply Finset.sum_congr rfl; intro t _
              apply Finset.sum_congr rfl; intro q _; ring
            rw [hlin]
            by_cases hj : j.val < L.d
            · rw [if_pos hj]
              let tj : Fin L.d := ⟨j.val, hj⟩
              have hsum : ∑ t : Fin L.d, coeff t * dotProduct (L.B.α ⟨t.val, lt_of_lt_of_le t.isLt L.hd⟩) (L.B.u j) =
                  coeff tj := by
                rw [Finset.sum_eq_single tj]
                · rw [L.B.biorth]; simp [tj]
                · intro t _ hne
                  rw [L.B.biorth]
                  have hne' : (⟨t.val, lt_of_lt_of_le t.isLt L.hd⟩ : Fin k) ≠ j :=
                    fun h => hne (Fin.ext (by simpa [tj] using congrArg Fin.val h))
                  simp [hne']
                · intro h; exact absurd (Finset.mem_univ tj) h
              rw [hsum]; dsimp [coeff, tj]; exact zmod2_add_self _
            · rw [if_neg hj]
              have hsum : ∑ t : Fin L.d, coeff t * dotProduct (L.B.α ⟨t.val, lt_of_lt_of_le t.isLt L.hd⟩) (L.B.u j) = 0 := by
                apply Finset.sum_eq_zero; intro t _
                rw [L.B.biorth]
                have hne' : (⟨t.val, lt_of_lt_of_le t.isLt L.hd⟩ : Fin k) ≠ j := by
                  intro h; have := congrArg Fin.val h; dsimp at this; omega
                simp [hne']
              rw [hsum, add_zero]
          let B1 : DualBasis k := L.B.swap d0 p
          have hB1_low : ∀ j : Fin k, j.val < d0.val → dotProduct β' (B1.u j) = 0 := by
            intro j hj
            dsimp [B1, DualBasis.swap]
            have hne1 : j ≠ d0 := fun h => by subst h; omega
            have hne2 : j ≠ p := fun h => by subst h; dsimp [d0] at hj; omega
            rw [Equiv.swap_apply_of_ne_of_ne hne1 hne2, hdot_β' j, if_pos hj]
          have hB1_d0 : dotProduct β' (B1.u d0) = 1 := by
            dsimp [B1, DualBasis.swap]
            rw [Equiv.swap_apply_left, hdot_β' p, if_neg (by omega)]
            exact zmod2_eq_one_of_ne_zero hpne
          let B2 : DualBasis k := B1.replaceAt d0 β' hB1_low hB1_d0
          have hB2_old : ∀ t : Fin L.d, B2.α ⟨t.val, lt_of_lt_of_le t.isLt L.hd⟩ = L.B.α ⟨t.val, lt_of_lt_of_le t.isLt L.hd⟩ := by
            intro t
            dsimp [B2, DualBasis.replaceAt, B1, DualBasis.swap]
            have hne1 : (⟨t.val, lt_of_lt_of_le t.isLt L.hd⟩ : Fin k) ≠ d0 := fun h => by
              have := congrArg Fin.val h; dsimp [d0] at this; omega
            have hne2 : (⟨t.val, lt_of_lt_of_le t.isLt L.hd⟩ : Fin k) ≠ p := fun h => by
              have := congrArg Fin.val h; dsimp at this; omega
            rw [if_neg hne1, Equiv.swap_apply_of_ne_of_ne hne1 hne2]
          have hB2_new : B2.α d0 = β' := by dsimp [B2, DualBasis.replaceAt]; simp

          let rSum := L.prog.pushSumFin L.d coeff L.rw L.hrw
          let rRhs0 := rSum.val.1.pushXor (L.yw f1) rSum.val.2
            (by have := L.hyw f1; have := rSum.property.1; omega) rSum.property.2.1
          let rRhs1 := rRhs0.val.1.pushNot rRhs0.val.2 rRhs0.property.2.1
          let rC0 := rRhs1.val.1.pushConst 0
          let rC1 := rC0.val.1.pushConst 1
          let Pfin : YProg k := rC1.val.1
          have hle_fin : L.prog.gates.length ≤ Pfin.gates.length :=
            le_trans rSum.property.1 (le_trans rRhs0.property.1
              (le_trans rRhs1.property.1 (le_trans rC0.property.1 rC1.property.1)))
          have hcost_fin : Pfin.gates.countP isPaid = L.prog.gates.countP isPaid := by
            dsimp [Pfin]
            rw [rC1.property.2.2.1, rC0.property.2.2.1, rRhs1.property.2.2.1,
                rRhs0.property.2.2.1, rSum.property.2.2.1]
          have hold_fin : ∀ y u, u < k + L.prog.gates.length → Pfin.val y u = L.prog.val y u := by
            intro y u hu
            have h1 := rSum.property.1; have h2 := rRhs0.property.1
            have h3 := rRhs1.property.1; have h4 := rC0.property.1
            dsimp [Pfin]
            rw [YProg.val,
                rC1.property.2.2.2.1 (bitsVec k y) (by simp [bitsVec]) u (by omega),
                rC0.property.2.2.2.1 (bitsVec k y) (by simp [bitsVec]) u (by omega),
                rRhs1.property.2.2.2.1 (bitsVec k y) (by simp [bitsVec]) u (by omega),
                rRhs0.property.2.2.2.1 (bitsVec k y) (by simp [bitsVec]) u (by omega)]
            exact rSum.property.2.2.2.1 y u hu
          have hval_rhs0 : ∀ y, Pfin.val y rRhs0.val.2 =
              L.prog.val y (L.yw f1) + ∑ t : Fin L.d, coeff t * L.prog.val y (L.rw t) := by
            intro y
            have h3 := rRhs1.property.1; have h4 := rC0.property.1; have hlt := rRhs0.property.2.1
            dsimp [Pfin]
            rw [YProg.val,
                rC1.property.2.2.2.1 (bitsVec k y) (by simp [bitsVec]) rRhs0.val.2 (by omega),
                rC0.property.2.2.2.1 (bitsVec k y) (by simp [bitsVec]) rRhs0.val.2 (by omega),
                rRhs1.property.2.2.2.1 (bitsVec k y) (by simp [bitsVec]) rRhs0.val.2 hlt,
                rRhs0.property.2.2.2.2 (bitsVec k y) (by simp [bitsVec])]
            change rSum.val.1.val y (L.yw f1) + rSum.val.1.val y rSum.val.2 = _
            rw [rSum.property.2.2.2.1 y (L.yw f1) (L.hyw f1), rSum.property.2.2.2.2 y]
          have hval_rhs1 : ∀ y, Pfin.val y rRhs1.val.2 =
              L.prog.val y (L.yw f1) + (∑ t : Fin L.d, coeff t * L.prog.val y (L.rw t)) + 1 := by
            intro y
            have h4 := rC0.property.1; have hlt := rRhs1.property.2.1
            dsimp [Pfin]
            rw [YProg.val,
                rC1.property.2.2.2.1 (bitsVec k y) (by simp [bitsVec]) rRhs1.val.2 (by omega),
                rC0.property.2.2.2.1 (bitsVec k y) (by simp [bitsVec]) rRhs1.val.2 hlt,
                rRhs1.property.2.2.2.2 (bitsVec k y) (by simp [bitsVec]),
                rRhs0.property.2.2.2.2 (bitsVec k y) (by simp [bitsVec])]
            change rSum.val.1.val y (L.yw f1) + rSum.val.1.val y rSum.val.2 + 1 = _
            rw [rSum.property.2.2.2.1 y (L.yw f1) (L.hyw f1), rSum.property.2.2.2.2 y]
          have hval_c0 : ∀ y, Pfin.val y rC0.val.2 = 0 := by
            intro y
            dsimp [Pfin]
            rw [YProg.val, rC1.property.2.2.2.1 (bitsVec k y) (by simp [bitsVec]) rC0.val.2 rC0.property.2.1]
            exact rC0.property.2.2.2.2 (bitsVec k y) (by simp [bitsVec])
          have hval_c1 : ∀ y, Pfin.val y rC1.val.2 = 1 := fun y =>
            rC1.property.2.2.2.2 (bitsVec k y) (by simp [bitsVec])
          let mkChild (γ : F) : RowLeaf k (2 * k + (gs ++ [g]).length) :=
            { d := L.d + 1
              hd := hd_lt
              B := B2
              prog := Pfin
              rw := fun t => if ht : t.val < L.d then L.rw ⟨t.val, ht⟩ else (if γ = 0 then rRhs0.val.2 else rRhs1.val.2)
              hrw := fun t => by
                dsimp [Pfin]
                split_ifs with ht
                · have := L.hrw ⟨t.val, ht⟩; dsimp [Pfin] at hle_fin; omega
                · have := rRhs0.property.2.1; have := rRhs1.property.1; have := rC0.property.1; have := rC1.property.1; omega
                · have := rRhs1.property.2.1; have := rC0.property.1; have := rC1.property.1; omega
              beta := fun w =>
                if hw : w.val < 2 * k + gs.length then L.beta ⟨w.val, hw⟩
                else if g.op = .and then (if γ = 0 then (fun _ => 0) else L.beta f2)
                else (if γ = 0 then L.beta f2 else (fun _ => 0))
              yw := fun w =>
                if hw : w.val < 2 * k + gs.length then L.yw ⟨w.val, hw⟩
                else if g.op = .and then (if γ = 0 then rC0.val.2 else L.yw f2)
                else (if γ = 0 then L.yw f2 else rC1.val.2)
              hyw := fun w => by
                dsimp [Pfin]
                split_ifs with hw
                · have := L.hyw ⟨w.val, hw⟩; dsimp [Pfin] at hle_fin; omega
                · have := rC0.property.2.1; have := rC1.property.1; omega
                · have := L.hyw f2; dsimp [Pfin] at hle_fin; omega
                · have := L.hyw f2; dsimp [Pfin] at hle_fin; omega
                · exact rC1.property.2.1 }
          have hchild_iff : ∀ γ x y,
              (mkChild γ).InLeaf x y ↔ L.InLeaf x y ∧ dotProduct β1 x + L.prog.val y (L.yw f1) = γ := by
            intro γ x y
            have hdot_β'x : dotProduct β' x =
                dotProduct β1 x + ∑ t : Fin L.d, coeff t * dotProduct (L.B.α ⟨t.val, lt_of_lt_of_le t.isLt L.hd⟩) x := by
              simp only [dotProduct, β', add_mul, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
              congr 1; rw [Finset.sum_comm]
              apply Finset.sum_congr rfl; intro t _
              apply Finset.sum_congr rfl; intro q _; ring
            have hrhs_val : Pfin.val y (if γ = 0 then rRhs0.val.2 else rRhs1.val.2) =
                L.prog.val y (L.yw f1) + (∑ t : Fin L.d, coeff t * L.prog.val y (L.rw t)) + γ := by
              rcases zmod2_cases γ with rfl | rfl
              · simp [hval_rhs0]
              · simp [hval_rhs1]
            constructor
            · intro h
              have hL : L.InLeaf x y := by
                intro t
                have ht := h ⟨t.val, by dsimp [mkChild]; omega⟩
                dsimp [mkChild] at ht
                simp only [t.isLt, ↓reduceDIte, ↓reduceIte] at ht
                rw [hB2_old t, hold_fin y (L.rw t) (L.hrw t)] at ht
                exact ht
              refine ⟨hL, ?_⟩
              have hlast := h ⟨L.d, Nat.lt_succ_self L.d⟩
              dsimp [mkChild] at hlast
              simp only [Nat.lt_irrefl L.d, ↓reduceDIte] at hlast
              rw [hB2_new, hrhs_val, hdot_β'x] at hlast
              have hsum_eq : (∑ t : Fin L.d, coeff t * dotProduct (L.B.α ⟨t.val, lt_of_lt_of_le t.isLt L.hd⟩) x) =
                  ∑ t : Fin L.d, coeff t * L.prog.val y (L.rw t) :=
                Finset.sum_congr rfl (fun t _ => by rw [hL t])
              rw [hsum_eq] at hlast
              let S := ∑ t : Fin L.d, coeff t * L.prog.val y (L.rw t)
              calc dotProduct β1 x + L.prog.val y (L.yw f1)
                  = (dotProduct β1 x + S) + (L.prog.val y (L.yw f1) + S) := by
                    have : (dotProduct β1 x + S) + (L.prog.val y (L.yw f1) + S) =
                        dotProduct β1 x + L.prog.val y (L.yw f1) + (S + S) := by ring
                    rw [this, zmod2_add_self, add_zero]
                _ = (L.prog.val y (L.yw f1) + S + γ) + (L.prog.val y (L.yw f1) + S) := by rw [hlast]
                _ = γ := by
                    have : (L.prog.val y (L.yw f1) + S + γ) + (L.prog.val y (L.yw f1) + S) =
                        γ + ((L.prog.val y (L.yw f1) + S) + (L.prog.val y (L.yw f1) + S)) := by ring
                    rw [this, zmod2_add_self, add_zero]
            · rintro ⟨hL, hγ⟩ t
              by_cases ht : t.val < L.d
              · dsimp [mkChild]
                simp only [ht, ↓reduceDIte]
                rw [hB2_old ⟨t.val, ht⟩, hold_fin y (L.rw ⟨t.val, ht⟩) (L.hrw ⟨t.val, ht⟩)]
                exact hL ⟨t.val, ht⟩
              · have hteq : t.val = L.d := by have := t.isLt; dsimp [mkChild] at this; omega
                have hfin : (⟨t.val, lt_of_lt_of_le t.isLt hd_lt⟩ : Fin k) = d0 := Fin.ext hteq
                dsimp [mkChild]
                simp only [ht, ↓reduceDIte]
                rw [hfin, hB2_new, hrhs_val, hdot_β'x]
                have hsum_eq : (∑ t' : Fin L.d, coeff t' * dotProduct (L.B.α ⟨t'.val, lt_of_lt_of_le t'.isLt L.hd⟩) x) =
                    ∑ t' : Fin L.d, coeff t' * L.prog.val y (L.rw t') :=
                  Finset.sum_congr rfl (fun t' _ => by rw [hL t'])
                rw [hsum_eq, ← hγ]
                have : L.prog.val y (L.yw f1) + (∑ t' : Fin L.d, coeff t' * L.prog.val y (L.rw t')) +
                    (dotProduct β1 x + L.prog.val y (L.yw f1)) =
                    dotProduct β1 x + (∑ t' : Fin L.d, coeff t' * L.prog.val y (L.rw t')) +
                      (L.prog.val y (L.yw f1) + L.prog.val y (L.yw f1)) := by ring
                rw [this, zmod2_add_self, add_zero]
          refine ⟨[mkChild 0, mkChild 1], ?_, ?_, ?_, ?_⟩
          · intro L' hL'
            simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hL'
            rw [hcnt_snoc, hpaid]
            rcases hL' with rfl | rfl <;> dsimp [mkChild] <;> rw [hcost_fin] <;> omega
          · intro x y hxy
            let γ : F := dotProduct β1 x + L.prog.val y (L.yw f1)
            rcases zmod2_cases γ with hγ0 | hγ1
            · refine ⟨⟨0, by simp⟩, (hchild_iff 0 x y).mpr ⟨hxy, hγ0⟩, ?_⟩
              intro idx hidx
              rcases (show idx.val = 0 ∨ idx.val = 1 by have := idx.isLt; simp at this; omega) with h0 | h1
              · exact Fin.ext h0
              · exfalso
                have hget : ([mkChild 0, mkChild 1].get idx) = mkChild 1 := by simp [List.get_eq_getElem, h1]
                rw [hget] at hidx
                have := ((hchild_iff 1 x y).mp hidx).2
                dsimp [γ] at hγ0; rw [hγ0] at this; exact zero_ne_one this
            · refine ⟨⟨1, by simp⟩, (hchild_iff 1 x y).mpr ⟨hxy, hγ1⟩, ?_⟩
              intro idx hidx
              rcases (show idx.val = 0 ∨ idx.val = 1 by have := idx.isLt; simp at this; omega) with h0 | h1
              · exfalso
                have hget : ([mkChild 0, mkChild 1].get idx) = mkChild 0 := by simp [List.get_eq_getElem, h0]
                rw [hget] at hidx
                have := ((hchild_iff 0 x y).mp hidx).2
                dsimp [γ] at hγ1; rw [hγ1] at this; exact one_ne_zero this
              · exact Fin.ext h1
          · intro L' hL' x y hxy
            simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hL'
            rcases hL' with rfl | rfl
            · exact ((hchild_iff 0 x y).mp hxy).1
            · exact ((hchild_iff 1 x y).mp hxy).1
          · intro L' hL' x y hxy w
            simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hL'
            have hcheck : ∀ γ : F, (mkChild γ).InLeaf x y →
                b2z ((wireList (gs ++ [g]) (bitsVec k x ++ bitsVec k y)).getD w.val false) =
                  dotProduct ((mkChild γ).beta w) x + (mkChild γ).prog.val y ((mkChild γ).yw w) := by
              intro γ hγmem
              have hch := (hchild_iff γ x y).mp hγmem
              by_cases hw : w.val < 2 * k + gs.length
              · dsimp [mkChild]; rw [dif_pos hw, dif_pos hw]
                have := hwire_pre x y ⟨w.val, hw⟩
                dsimp at this
                rw [this, hold_fin y (L.yw ⟨w.val, hw⟩) (L.hyw ⟨w.val, hw⟩)]
                exact hLsem x y hch.1 ⟨w.val, hw⟩
              · dsimp [mkChild]; rw [dif_neg hw, dif_neg hw, hfin_last w hw, hsym x y]
                have hf1 : b2z ((wireList gs (bitsVec k x ++ bitsVec k y)).getD f1.val false) = γ := by
                  rw [hLsem x y hch.1 f1]; exact hch.2
                have hf2 : b2z ((wireList gs (bitsVec k x ++ bitsVec k y)).getD f2.val false) =
                    dotProduct (L.beta f2) x + L.prog.val y (L.yw f2) := hLsem x y hch.1 f2
                rw [hf1, hf2]
                by_cases hop : g.op = .and
                · simp only [hop, ↓reduceIte]
                  rcases zmod2_cases γ with rfl | rfl
                  · simp [hval_c0, dotProduct]
                  · simp [hold_fin y (L.yw f2) (L.hyw f2)]
                · simp only [hop, ↓reduceIte]
                  rcases zmod2_cases γ with rfl | rfl
                  · simp [hold_fin y (L.yw f2) (L.hyw f2)]
                  · simp only [show ¬ ((1 : F) = 0) by decide, ↓reduceIte, hval_c1]
                    have h0 : dotProduct (fun _ : Fin k => (0 : F)) x = 0 := by simp [dotProduct]
                    rw [h0, zero_add]
                    ring_nf
                    rw [show (2 : F) = 0 by decide]; ring
            rcases hL' with rfl | rfl
            · exact hcheck 0 hxy
            · exact hcheck 1 hxy
        by_cases ha_out : ∃ p : Fin k, L.d ≤ p.val ∧ dotProduct (L.beta fa) (L.B.u p) ≠ 0
        · exact hbranch_on fa fb hgeval ha_out
        · by_cases hb_out : ∃ p : Fin k, L.d ≤ p.val ∧ dotProduct (L.beta fb) (L.B.u p) ≠ 0
          · refine hbranch_on fb fa (fun x y => ?_) hb_out
            rw [hgeval x y]; split_ifs <;> ring
          · push Not at ha_out hb_out
            have hexp_in : ∀ (f0 : Fin (2 * k + gs.length)),
                (∀ p : Fin k, L.d ≤ p.val → dotProduct (L.beta f0) (L.B.u p) = 0) →
                ∀ x y, L.InLeaf x y →
                  dotProduct (L.beta f0) x =
                    ∑ t : Fin L.d, dotProduct (L.beta f0) (L.B.u ⟨t.val, lt_of_lt_of_le t.isLt L.hd⟩) *
                      L.prog.val y (L.rw t) := by
              intro f0 hf0 x y hxy
              conv_lhs => rw [L.B.expand_α (L.beta f0)]
              have hdot : dotProduct (fun q => ∑ i : Fin k, dotProduct (L.beta f0) (L.B.u i) * L.B.α i q) x =
                  ∑ i : Fin k, dotProduct (L.beta f0) (L.B.u i) * dotProduct (L.B.α i) x := by
                calc dotProduct (fun q => ∑ i : Fin k, dotProduct (L.beta f0) (L.B.u i) * L.B.α i q) x
                    = ∑ q : Fin k, ∑ i : Fin k, dotProduct (L.beta f0) (L.B.u i) * L.B.α i q * x q := by
                      dsimp only [dotProduct]
                      apply Finset.sum_congr rfl; intro q _; rw [Finset.sum_mul]
                  _ = ∑ i : Fin k, ∑ q : Fin k, dotProduct (L.beta f0) (L.B.u i) * (L.B.α i q * x q) := by
                      rw [Finset.sum_comm]
                      apply Finset.sum_congr rfl; intro i _
                      apply Finset.sum_congr rfl; intro q _; ring
                  _ = ∑ i : Fin k, dotProduct (L.beta f0) (L.B.u i) * dotProduct (L.B.α i) x := by
                      apply Finset.sum_congr rfl; intro i _; dsimp only [dotProduct]; rw [Finset.mul_sum]
              rw [hdot]
              have hsplit : ∑ i : Fin k, dotProduct (L.beta f0) (L.B.u i) * dotProduct (L.B.α i) x =
                  ∑ i ∈ Finset.univ.filter (fun i : Fin k => i.val < L.d),
                    dotProduct (L.beta f0) (L.B.u i) * dotProduct (L.B.α i) x := by
                rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin k => i.val < L.d)]
                have hzero : ∑ i ∈ Finset.univ.filter (fun i : Fin k => ¬ i.val < L.d),
                    dotProduct (L.beta f0) (L.B.u i) * dotProduct (L.B.α i) x = 0 := by
                  apply Finset.sum_eq_zero; intro i hi
                  have hge : L.d ≤ i.val := by have := (Finset.mem_filter.mp hi).2; omega
                  rw [hf0 i hge, zero_mul]
                rw [hzero, add_zero]
              rw [hsplit]
              symm
              refine Finset.sum_bij (fun t _ => (⟨t.val, lt_of_lt_of_le t.isLt L.hd⟩ : Fin k)) ?_ ?_ ?_ ?_
              · intro t _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, t.isLt⟩
              · intro t1 _ t2 _ h; exact Fin.ext (by simpa using congrArg Fin.val h)
              · intro i hi
                have hlt : i.val < L.d := (Finset.mem_filter.mp hi).2
                exact ⟨⟨i.val, hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩
              · intro t _; rw [hxy t]
            let ca : Fin L.d → F := fun t => dotProduct (L.beta fa) (L.B.u ⟨t.val, lt_of_lt_of_le t.isLt L.hd⟩)
            let cb : Fin L.d → F := fun t => dotProduct (L.beta fb) (L.B.u ⟨t.val, lt_of_lt_of_le t.isLt L.hd⟩)
            let rSa := L.prog.pushSumFin L.d ca L.rw L.hrw
            let rWa := rSa.val.1.pushXor (L.yw fa) rSa.val.2
              (by have := L.hyw fa; have := rSa.property.1; omega) rSa.property.2.1
            let rSb := rWa.val.1.pushSumFin L.d cb L.rw (fun t => by
              have := L.hrw t; have := rSa.property.1; have := rWa.property.1; omega)
            let rWb := rSb.val.1.pushXor (L.yw fb) rSb.val.2
              (by have := L.hyw fb; have := rSa.property.1; have := rWa.property.1; have := rSb.property.1; omega)
              rSb.property.2.1
            have hwa_lt : rWa.val.2 < k + rWb.val.1.gates.length := by
              have := rWa.property.2.1; have := rSb.property.1; have := rWb.property.1; omega
            let rPaid := rWb.val.1.pushPaid g.op hop_ab rWa.val.2 rWb.val.2 hwa_lt rWb.property.2.1
            have hle_all : L.prog.gates.length ≤ rPaid.val.1.gates.length :=
              le_trans rSa.property.1 (le_trans rWa.property.1
                (le_trans rSb.property.1 (le_trans rWb.property.1 rPaid.property.1)))
            have hold_all : ∀ y u, u < k + L.prog.gates.length → rPaid.val.1.val y u = L.prog.val y u := by
              intro y u hu
              have h1 := rSa.property.1; have h2 := rWa.property.1
              have h3 := rSb.property.1; have h4 := rWb.property.1
              rw [YProg.val,
                  rPaid.property.2.2.2.1 (bitsVec k y) (by simp [bitsVec]) u (by omega),
                  rWb.property.2.2.2.1 (bitsVec k y) (by simp [bitsVec]) u (by omega)]
              change rSb.val.1.val y u = L.prog.val y u
              rw [rSb.property.2.2.2.1 y u (by omega)]
              rw [YProg.val, rWa.property.2.2.2.1 (bitsVec k y) (by simp [bitsVec]) u (by omega)]
              exact rSa.property.2.2.2.1 y u hu
            let L1 : RowLeaf k (2 * k + (gs ++ [g]).length) :=
              { d := L.d
                hd := L.hd
                B := L.B
                prog := rPaid.val.1
                rw := L.rw
                hrw := fun t => by have := L.hrw t; omega
                beta := fun w => if hw : w.val < 2 * k + gs.length then L.beta ⟨w.val, hw⟩ else (fun _ => 0)
                yw := fun w => if hw : w.val < 2 * k + gs.length then L.yw ⟨w.val, hw⟩ else rPaid.val.2
                hyw := fun w => by
                  by_cases hw : w.val < 2 * k + gs.length
                  · rw [dif_pos hw]; have := L.hyw ⟨w.val, hw⟩; omega
                  · rw [dif_neg hw]; exact rPaid.property.2.1 }
            have hIn_iff : ∀ x y, L1.InLeaf x y ↔ L.InLeaf x y := by
              intro x y; simp only [RowLeaf.InLeaf, L1]
              apply forall_congr'; intro t
              rw [hold_all y (L.rw t) (L.hrw t)]
            refine ⟨[L1], ?_, ?_, ?_, ?_⟩
            · intro L' hL'
              rw [List.mem_singleton.mp hL']
              dsimp [L1]
              rw [rPaid.property.2.2.1, rWb.property.2.2.1, rSb.property.2.2.1,
                  rWa.property.2.2.1, rSa.property.2.2.1, hcnt_snoc, hpaid]
              simp; omega
            · intro x y hxy
              refine ⟨⟨0, by simp⟩, (hIn_iff x y).mpr hxy, fun idx _ => Fin.ext (by have := idx.isLt; simp at this ⊢)⟩
            · intro L' hL' x y hxy
              rw [List.mem_singleton.mp hL'] at hxy
              exact (hIn_iff x y).mp hxy
            · intro L' hL' x y hxy w
              rw [List.mem_singleton.mp hL'] at hxy ⊢
              have hxy0 := (hIn_iff x y).mp hxy
              dsimp [L1]
              by_cases hw : w.val < 2 * k + gs.length
              · rw [dif_pos hw, dif_pos hw]
                have := hwire_pre x y ⟨w.val, hw⟩
                dsimp at this
                rw [this, hold_all y (L.yw ⟨w.val, hw⟩) (L.hyw ⟨w.val, hw⟩)]
                exact hLsem x y hxy0 ⟨w.val, hw⟩
              · rw [dif_neg hw, dif_neg hw, hfin_last w hw, hgeval x y]
                have hrp := rPaid.property.2.2.2.2 (bitsVec k y) (by simp [bitsVec])
                have h0 : dotProduct (fun _ : Fin k => (0 : F)) x = 0 := by simp [dotProduct]
                rw [h0, zero_add]
                change _ = rPaid.val.1.valList (bitsVec k y) rPaid.val.2
                rw [hrp]
                have hval_a : rWb.val.1.valList (bitsVec k y) rWa.val.2 =
                    b2z ((wireList gs (bitsVec k x ++ bitsVec k y)).getD a false) := by
                  have h1 := rSa.property.1; have h2 := rWa.property.1; have h3 := rSb.property.1
                  rw [rWb.property.2.2.2.1 (bitsVec k y) (by simp [bitsVec]) rWa.val.2 (by have := rWa.property.2.1; omega)]
                  change rSb.val.1.val y rWa.val.2 = _
                  rw [rSb.property.2.2.2.1 y rWa.val.2 rWa.property.2.1]
                  change rWa.val.1.valList (bitsVec k y) rWa.val.2 = _
                  rw [rWa.property.2.2.2.2 (bitsVec k y) (by simp [bitsVec])]
                  change rSa.val.1.val y (L.yw fa) + rSa.val.1.val y rSa.val.2 = _
                  rw [rSa.property.2.2.2.1 y (L.yw fa) (L.hyw fa), rSa.property.2.2.2.2 y]
                  have hsem_a := hLsem x y hxy0 fa
                  dsimp [fa] at hsem_a
                  rw [hsem_a, hexp_in fa ha_out x y hxy0]
                  dsimp [ca]; ring
                have hval_b : rWb.val.1.valList (bitsVec k y) rWb.val.2 =
                    b2z ((wireList gs (bitsVec k x ++ bitsVec k y)).getD b false) := by
                  have h1 := rSa.property.1; have h2 := rWa.property.1; have h3 := rSb.property.1
                  rw [rWb.property.2.2.2.2 (bitsVec k y) (by simp [bitsVec])]
                  change rSb.val.1.val y (L.yw fb) + rSb.val.1.val y rSb.val.2 = _
                  rw [rSb.property.2.2.2.1 y (L.yw fb) (by have := L.hyw fb; omega), rSb.property.2.2.2.2 y]
                  change rWa.val.1.valList (bitsVec k y) (L.yw fb) + _ = _
                  rw [rWa.property.2.2.2.1 (bitsVec k y) (by simp [bitsVec]) (L.yw fb) (by have := L.hyw fb; omega)]
                  change rSa.val.1.val y (L.yw fb) + _ = _
                  rw [rSa.property.2.2.2.1 y (L.yw fb) (L.hyw fb)]
                  have hsum_b : ∑ t : Fin L.d, cb t * rWa.val.1.val y (L.rw t) =
                      ∑ t : Fin L.d, cb t * L.prog.val y (L.rw t) := by
                    apply Finset.sum_congr rfl; intro t _
                    change cb t * rWa.val.1.valList (bitsVec k y) (L.rw t) = _
                    rw [rWa.property.2.2.2.1 (bitsVec k y) (by simp [bitsVec]) (L.rw t) (by have := L.hrw t; omega)]
                    change cb t * rSa.val.1.val y (L.rw t) = _
                    rw [rSa.property.2.2.2.1 y (L.rw t) (L.hrw t)]
                  rw [hsum_b]
                  have hsem_b := hLsem x y hxy0 fb
                  dsimp [fb] at hsem_b
                  rw [hsem_b, hexp_in fb hb_out x y hxy0]
                  dsimp [cb]; ring
                rw [hval_a, hval_b]

    let expandFun (L : RowLeaf k (2 * k + gs.length)) : List (RowLeaf k (2 * k + (gs ++ [g]).length)) :=
      if hL : L ∈ leaves then Classical.choose (hexpand L (hcost L hL) (hsem L hL)) else []
    let leaves' := leaves.flatMap expandFun
    refine ⟨leaves', ?_, ?_, ?_⟩
    · intro L' hL'
      obtain ⟨L, hL, hmem⟩ := List.mem_flatMap.mp hL'
      dsimp [expandFun] at hmem; rw [dif_pos hL] at hmem
      exact (Classical.choose_spec (hexpand L (hcost L hL) (hsem L hL))).1 L' hmem
    · intro x y
      exact list_flatMap_partition leaves expandFun
        (fun L (p : (Fin k → F) × (Fin k → F)) => L.InLeaf p.1 p.2)
        (fun L' (p : (Fin k → F) × (Fin k → F)) => L'.InLeaf p.1 p.2)
        (fun p => hpart p.1 p.2)
        (fun L hL p hp => by
          dsimp [expandFun]; rw [dif_pos hL]
          exact (Classical.choose_spec (hexpand L (hcost L hL) (hsem L hL))).2.1 p.1 p.2 hp)
        (fun L hL L' hmem p hp => by
          dsimp [expandFun] at hmem; rw [dif_pos hL] at hmem
          exact (Classical.choose_spec (hexpand L (hcost L hL) (hsem L hL))).2.2.1 L' hmem p.1 p.2 hp)
        (x, y)
    · intro L' hL' x y hxy w
      obtain ⟨L, hL, hmem⟩ := List.mem_flatMap.mp hL'
      dsimp [expandFun] at hmem; rw [dif_pos hL] at hmem
      exact (Classical.choose_spec (hexpand L (hcost L hL) (hsem L hL))).2.2.2 L' hmem x y hxy w

lemma row_leaf_bound {k m s nw : ℕ} (pos : Fin m × Fin 3 ↪ Fin k)
    (L : RowLeaf k nw) (hLcost : L.d + L.prog.gates.countP isPaid ≤ s)
    (βout : Fin k → F) (ywOut : ℕ) (hywOut : ywOut < k + L.prog.gates.length) :
    let g : (Fin k → F) → F := fun y => ∑ i : Fin m, y (pos (i, 0)) * y (pos (i, 1)) * y (pos (i, 2))
    let Sset : Finset ((Fin k → F) × (Fin k → F)) := Finset.univ.filter (fun p => L.InLeaf p.1 p.2)
    let b := k - s
    let j := m - (b + (s - k))
    2 ^ b * 4 ^ j *
      (∑ p ∈ Sset, chi (dotProduct βout p.1 + L.prog.val p.2 ywOut + dotProduct p.1 p.2 + g p.2)).natAbs
        ≤ Sset.card * 3 ^ j := by
  classical
  dsimp only
  let g : (Fin k → F) → F := fun y => ∑ i : Fin m, y (pos (i, 0)) * y (pos (i, 1)) * y (pos (i, 2))
  let Sset : Finset ((Fin k → F) × (Fin k → F)) := Finset.univ.filter (fun p => L.InLeaf p.1 p.2)
  let l := k - L.d
  have hdl : L.d + l = k := Nat.add_sub_of_le L.hd

  let x0 (y : Fin k → F) : Fin k → F :=
    fun p => ∑ t : Fin L.d, L.prog.val y (L.rw t) * L.B.u ⟨t.val, lt_of_lt_of_le t.isLt L.hd⟩ p
  let xOf (y : Fin k → F) (c : Fin l → F) : Fin k → F :=
    fun p => x0 y p + ∑ r : Fin l, c r * L.B.u ⟨L.d + r.val, by omega⟩ p
  have hxOf_dot_low : ∀ y c (t : Fin L.d),
      dotProduct (L.B.α ⟨t.val, lt_of_lt_of_le t.isLt L.hd⟩) (xOf y c) = L.prog.val y (L.rw t) := by
    intro y c t
    dsimp [xOf, x0, dotProduct]
    simp_rw [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    have h1 : ∑ p : Fin k, ∑ t' : Fin L.d, L.B.α ⟨t.val, lt_of_lt_of_le t.isLt L.hd⟩ p *
        (L.prog.val y (L.rw t') * L.B.u ⟨t'.val, lt_of_lt_of_le t'.isLt L.hd⟩ p) =
        L.prog.val y (L.rw t) := by
      rw [Finset.sum_comm]
      rw [Finset.sum_eq_single t]
      · have : ∑ p : Fin k, L.B.α ⟨t.val, lt_of_lt_of_le t.isLt L.hd⟩ p *
            (L.prog.val y (L.rw t) * L.B.u ⟨t.val, lt_of_lt_of_le t.isLt L.hd⟩ p) =
            L.prog.val y (L.rw t) * dotProduct (L.B.α ⟨t.val, lt_of_lt_of_le t.isLt L.hd⟩)
              (L.B.u ⟨t.val, lt_of_lt_of_le t.isLt L.hd⟩) := by
          dsimp [dotProduct]; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro p _; ring
        rw [this, L.B.biorth]; simp
      · intro t' _ hne
        have : ∑ p : Fin k, L.B.α ⟨t.val, lt_of_lt_of_le t.isLt L.hd⟩ p *
            (L.prog.val y (L.rw t') * L.B.u ⟨t'.val, lt_of_lt_of_le t'.isLt L.hd⟩ p) =
            L.prog.val y (L.rw t') * dotProduct (L.B.α ⟨t.val, lt_of_lt_of_le t.isLt L.hd⟩)
              (L.B.u ⟨t'.val, lt_of_lt_of_le t'.isLt L.hd⟩) := by
          dsimp [dotProduct]; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro p _; ring
        rw [this, L.B.biorth]
        have hne' : (⟨t.val, lt_of_lt_of_le t.isLt L.hd⟩ : Fin k) ≠ ⟨t'.val, lt_of_lt_of_le t'.isLt L.hd⟩ :=
          fun h => hne (Fin.ext (congrArg Fin.val h).symm)
        simp [hne']
      · intro h; exact absurd (Finset.mem_univ t) h
    have h2 : ∑ p : Fin k, ∑ r : Fin l, L.B.α ⟨t.val, lt_of_lt_of_le t.isLt L.hd⟩ p *
        (c r * L.B.u ⟨L.d + r.val, by omega⟩ p) = 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_eq_zero; intro r _
      have : ∑ p : Fin k, L.B.α ⟨t.val, lt_of_lt_of_le t.isLt L.hd⟩ p *
          (c r * L.B.u ⟨L.d + r.val, by omega⟩ p) =
          c r * dotProduct (L.B.α ⟨t.val, lt_of_lt_of_le t.isLt L.hd⟩) (L.B.u ⟨L.d + r.val, by omega⟩) := by
        dsimp [dotProduct]; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro p _; ring
      rw [this, L.B.biorth]
      have hne : (⟨t.val, lt_of_lt_of_le t.isLt L.hd⟩ : Fin k) ≠ ⟨L.d + r.val, by omega⟩ := by
        intro h; have := congrArg Fin.val h; dsimp at this; omega
      simp [hne]
    rw [h1, h2, add_zero]
  have hxOf_dot_high : ∀ y c (r : Fin l),
      dotProduct (L.B.α ⟨L.d + r.val, by omega⟩) (xOf y c) = c r := by
    intro y c r
    dsimp [xOf, x0, dotProduct]
    simp_rw [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    have h1 : ∑ p : Fin k, ∑ t : Fin L.d, L.B.α ⟨L.d + r.val, by omega⟩ p *
        (L.prog.val y (L.rw t) * L.B.u ⟨t.val, lt_of_lt_of_le t.isLt L.hd⟩ p) = 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_eq_zero; intro t _
      have : ∑ p : Fin k, L.B.α ⟨L.d + r.val, by omega⟩ p *
          (L.prog.val y (L.rw t) * L.B.u ⟨t.val, lt_of_lt_of_le t.isLt L.hd⟩ p) =
          L.prog.val y (L.rw t) * dotProduct (L.B.α ⟨L.d + r.val, by omega⟩)
            (L.B.u ⟨t.val, lt_of_lt_of_le t.isLt L.hd⟩) := by
        dsimp [dotProduct]; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro p _; ring
      rw [this, L.B.biorth]
      have hne : (⟨L.d + r.val, by omega⟩ : Fin k) ≠ ⟨t.val, lt_of_lt_of_le t.isLt L.hd⟩ := by
        intro h; have := congrArg Fin.val h; dsimp at this; omega
      simp [hne]
    have h2 : ∑ p : Fin k, ∑ r' : Fin l, L.B.α ⟨L.d + r.val, by omega⟩ p *
        (c r' * L.B.u ⟨L.d + r'.val, by omega⟩ p) = c r := by
      rw [Finset.sum_comm]
      rw [Finset.sum_eq_single r]
      · have : ∑ p : Fin k, L.B.α ⟨L.d + r.val, by omega⟩ p * (c r * L.B.u ⟨L.d + r.val, by omega⟩ p) =
            c r * dotProduct (L.B.α ⟨L.d + r.val, by omega⟩) (L.B.u ⟨L.d + r.val, by omega⟩) := by
          dsimp [dotProduct]; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro p _; ring
        rw [this, L.B.biorth]; simp
      · intro r' _ hne
        have : ∑ p : Fin k, L.B.α ⟨L.d + r.val, by omega⟩ p * (c r' * L.B.u ⟨L.d + r'.val, by omega⟩ p) =
            c r' * dotProduct (L.B.α ⟨L.d + r.val, by omega⟩) (L.B.u ⟨L.d + r'.val, by omega⟩) := by
          dsimp [dotProduct]; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro p _; ring
        rw [this, L.B.biorth]
        have hne' : (⟨L.d + r.val, by omega⟩ : Fin k) ≠ ⟨L.d + r'.val, by omega⟩ := by
          intro h; have := congrArg Fin.val h; dsimp at this; exact hne (Fin.ext (by omega))
        simp [hne']
      · intro h; exact absurd (Finset.mem_univ r) h
    rw [h1, h2, zero_add]
  have hSset_bij : ∀ (f : (Fin k → F) × (Fin k → F) → ℤ),
      ∑ p ∈ Sset, f p = ∑ y : Fin k → F, ∑ c : Fin l → F, f (xOf y c, y) := by
    intro f
    have hprod_sum : (∑ y : Fin k → F, ∑ c : Fin l → F, f (xOf y c, y)) =
        ∑ p : (Fin k → F) × (Fin l → F), f (xOf p.1 p.2, p.1) :=
      (Fintype.sum_prod_type (fun p : (Fin k → F) × (Fin l → F) => f (xOf p.1 p.2, p.1))).symm
    rw [hprod_sum]
    symm
    refine Finset.sum_bij (fun (p : (Fin k → F) × (Fin l → F)) _ => (xOf p.1 p.2, p.1)) ?_ ?_ ?_ ?_
    · intro ⟨y, c⟩ _
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxOf_dot_low y c⟩
    · intro ⟨y1, c1⟩ _ ⟨y2, c2⟩ _ h
      have hy : y1 = y2 := congrArg Prod.snd h
      subst hy
      have hx : xOf y1 c1 = xOf y1 c2 := congrArg Prod.fst h
      refine Prod.ext rfl ?_
      funext r
      have := congrArg (dotProduct (L.B.α ⟨L.d + r.val, by omega⟩)) hx
      rw [hxOf_dot_high, hxOf_dot_high] at this
      exact this
    · intro ⟨x, y⟩ hxy
      have hxy' : L.InLeaf x y := (Finset.mem_filter.mp hxy).2
      let c : Fin l → F := fun r => dotProduct (L.B.α ⟨L.d + r.val, by omega⟩) x
      refine ⟨(y, c), Finset.mem_univ _, Prod.ext ?_ rfl⟩
      conv_rhs => rw [L.B.expand_u x]
      funext p
      dsimp [xOf, x0, c]
      have hsplit : ∑ i : Fin k, dotProduct (L.B.α i) x * L.B.u i p =
          (∑ i ∈ Finset.univ.filter (fun i : Fin k => i.val < L.d), dotProduct (L.B.α i) x * L.B.u i p) +
          (∑ i ∈ Finset.univ.filter (fun i : Fin k => ¬ i.val < L.d), dotProduct (L.B.α i) x * L.B.u i p) :=
        (Finset.sum_filter_add_sum_filter_not _ _ _).symm
      rw [hsplit]
      congr 1
      · refine Finset.sum_bij (fun t _ => (⟨t.val, lt_of_lt_of_le t.isLt L.hd⟩ : Fin k)) ?_ ?_ ?_ ?_
        · intro t _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, t.isLt⟩
        · intro t1 _ t2 _ h; exact Fin.ext (by simpa using congrArg Fin.val h)
        · intro i hi; exact ⟨⟨i.val, (Finset.mem_filter.mp hi).2⟩, Finset.mem_univ _, Fin.ext rfl⟩
        · intro t _; rw [hxy' t]
      · refine Finset.sum_bij (fun r _ => (⟨L.d + r.val, by omega⟩ : Fin k)) ?_ ?_ ?_ ?_
        · intro r _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp; omega⟩
        · intro r1 _ r2 _ h; exact Fin.ext (by have := congrArg Fin.val h; dsimp at this; omega)
        · intro i hi
          have hge : L.d ≤ i.val := by have := (Finset.mem_filter.mp hi).2; omega
          exact ⟨⟨i.val - L.d, by omega⟩, Finset.mem_univ _, Fin.ext (by dsimp; omega)⟩
        · intro r _; rfl
    · intro _ _; rfl
  have hSset_card : Sset.card = 2 ^ (k + l) := by
    have h1 := hSset_bij (fun _ => (1 : ℤ))
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      Fintype.card_fun, ZMod.card 2, Fintype.card_fin] at h1
    have h3 : Sset.card = 2 ^ k * 2 ^ l := by
      have h2 : (Sset.card : ℤ) = ((2 ^ k * 2 ^ l : ℕ) : ℤ) := by
        push_cast at h1 ⊢; linarith
      exact Int.ofNat.inj h2
    rw [h3, pow_add]

  let eqs0 : Fin l → (Fin k → F) × F := fun r =>
    (L.B.u ⟨L.d + r.val, by omega⟩, dotProduct βout (L.B.u ⟨L.d + r.val, by omega⟩))

  let Qfull (y : Fin k → F) : F :=
    (∑ t : Fin L.d, L.prog.val y (L.rw t) * dotProduct (fun q => βout q + y q) (L.B.u ⟨t.val, lt_of_lt_of_le t.isLt L.hd⟩)) +
    L.prog.val y ywOut
  have hinner : ∀ y : Fin k → F,
      (∑ c : Fin l → F, chi (dotProduct βout (xOf y c) + L.prog.val y ywOut + dotProduct (xOf y c) y + g y)) =
      if y ∈ AffSet eqs0 then (2 : ℤ) ^ l * chi (Qfull y + g y) else 0 := by
    intro y
    have hexp : ∀ c : Fin l → F,
        dotProduct βout (xOf y c) + L.prog.val y ywOut + dotProduct (xOf y c) y + g y =
        (Qfull y + g y) + ∑ r : Fin l, c r * dotProduct (fun q => βout q + y q) (L.B.u ⟨L.d + r.val, by omega⟩) := by
      intro c
      have hxy : dotProduct βout (xOf y c) + dotProduct (xOf y c) y =
          dotProduct (fun q => βout q + y q) (xOf y c) := by
        simp only [dotProduct, add_mul, Finset.sum_add_distrib]
        congr 1; apply Finset.sum_congr rfl; intro q _; ring
      have hdot_xOf : dotProduct (fun q => βout q + y q) (xOf y c) =
          (∑ t : Fin L.d, L.prog.val y (L.rw t) * dotProduct (fun q => βout q + y q) (L.B.u ⟨t.val, lt_of_lt_of_le t.isLt L.hd⟩)) +
          ∑ r : Fin l, c r * dotProduct (fun q => βout q + y q) (L.B.u ⟨L.d + r.val, by omega⟩) := by
        dsimp [xOf, x0, dotProduct]
        simp_rw [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
        congr 1 <;> (rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro _ _; apply Finset.sum_congr rfl; intro _ _; ring)
      calc dotProduct βout (xOf y c) + L.prog.val y ywOut + dotProduct (xOf y c) y + g y
          = (dotProduct βout (xOf y c) + dotProduct (xOf y c) y) + L.prog.val y ywOut + g y := by ring
        _ = dotProduct (fun q => βout q + y q) (xOf y c) + L.prog.val y ywOut + g y := by rw [hxy]
        _ = _ := by rw [hdot_xOf]; dsimp [Qfull]; ring
    simp_rw [hexp, chi_add]
    rw [← Finset.mul_sum, sum_chi_dot_fin]
    have hcond : (∀ r : Fin l, dotProduct (fun q => βout q + y q) (L.B.u ⟨L.d + r.val, by omega⟩) = 0) ↔
        y ∈ AffSet eqs0 := by
      simp only [AffSet, eqs0, Finset.mem_filter, Finset.mem_univ, true_and]
      apply forall_congr'; intro r
      have h1 : dotProduct (fun q => βout q + y q) (L.B.u ⟨L.d + r.val, by omega⟩) =
          dotProduct βout (L.B.u ⟨L.d + r.val, by omega⟩) + ∑ q : Fin k, L.B.u ⟨L.d + r.val, by omega⟩ q * y q := by
        simp only [dotProduct, add_mul, Finset.sum_add_distrib]
        congr 1; apply Finset.sum_congr rfl; intro q _; ring
      rw [h1]
      constructor
      · intro h
        calc ∑ q : Fin k, L.B.u ⟨L.d + r.val, by omega⟩ q * y q
            = (dotProduct βout (L.B.u ⟨L.d + r.val, by omega⟩) + ∑ q : Fin k, L.B.u ⟨L.d + r.val, by omega⟩ q * y q) +
              dotProduct βout (L.B.u ⟨L.d + r.val, by omega⟩) := by
              rw [add_comm (dotProduct _ _), add_assoc, zmod2_add_self, add_zero]
          _ = dotProduct βout (L.B.u ⟨L.d + r.val, by omega⟩) := by rw [h, zero_add]
      · intro h; rw [h, zmod2_add_self]
    by_cases hy : y ∈ AffSet eqs0
    · rw [if_pos hy, if_pos (hcond.mpr hy), mul_comm]
    · rw [if_neg hy, if_neg (fun h => hy (hcond.mp h)), mul_zero]

  have hA0_card : (AffSet eqs0).card = 2 ^ L.d := by
    let yOf (c : Fin L.d → F) : Fin k → F :=
      fun q => βout q + ∑ t : Fin L.d, c t * L.B.α ⟨t.val, lt_of_lt_of_le t.isLt L.hd⟩ q
    have hbij : ∑ _y ∈ AffSet eqs0, (1 : ℕ) = ∑ _c : Fin L.d → F, (1 : ℕ) := by
      symm
      refine Finset.sum_bij (fun c _ => yOf c) ?_ ?_ ?_ ?_
      · intro c _
        simp only [AffSet, eqs0, Finset.mem_filter, Finset.mem_univ, true_and]
        intro r
        have hdot : ∑ i : Fin k, L.B.u ⟨L.d + r.val, by omega⟩ i * yOf c i =
            dotProduct βout (L.B.u ⟨L.d + r.val, by omega⟩) +
            ∑ t : Fin L.d, c t * dotProduct (L.B.α ⟨t.val, lt_of_lt_of_le t.isLt L.hd⟩) (L.B.u ⟨L.d + r.val, by omega⟩) := by
          dsimp [yOf, dotProduct]
          simp_rw [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
          congr 1
          · apply Finset.sum_congr rfl; intro i _; ring
          · rw [Finset.sum_comm]
            apply Finset.sum_congr rfl; intro t _
            apply Finset.sum_congr rfl; intro i _; ring
        rw [hdot]
        have hz : ∑ t : Fin L.d, c t * dotProduct (L.B.α ⟨t.val, lt_of_lt_of_le t.isLt L.hd⟩) (L.B.u ⟨L.d + r.val, by omega⟩) = 0 := by
          apply Finset.sum_eq_zero; intro t _
          rw [L.B.biorth]
          have hne : (⟨t.val, lt_of_lt_of_le t.isLt L.hd⟩ : Fin k) ≠ ⟨L.d + r.val, by omega⟩ := by
            intro h; have := congrArg Fin.val h; dsimp at this; omega
          simp [hne]
        rw [hz, add_zero]
      · intro c1 _ c2 _ h
        funext t
        have hdot := congrArg (fun v => dotProduct v (L.B.u ⟨t.val, lt_of_lt_of_le t.isLt L.hd⟩)) h
        have heval : ∀ c : Fin L.d → F,
            dotProduct (yOf c) (L.B.u ⟨t.val, lt_of_lt_of_le t.isLt L.hd⟩) =
            dotProduct βout (L.B.u ⟨t.val, lt_of_lt_of_le t.isLt L.hd⟩) + c t := by
          intro c
          dsimp [yOf, dotProduct]
          simp_rw [add_mul, Finset.sum_add_distrib, Finset.sum_mul]
          congr 1
          rw [Finset.sum_comm, Finset.sum_eq_single t]
          · have : ∑ q : Fin k, c t * L.B.α ⟨t.val, lt_of_lt_of_le t.isLt L.hd⟩ q *
                L.B.u ⟨t.val, lt_of_lt_of_le t.isLt L.hd⟩ q =
                c t * dotProduct (L.B.α ⟨t.val, lt_of_lt_of_le t.isLt L.hd⟩)
                  (L.B.u ⟨t.val, lt_of_lt_of_le t.isLt L.hd⟩) := by
              dsimp [dotProduct]; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro q _; ring
            rw [this, L.B.biorth]; simp
          · intro t' _ hne
            have : ∑ q : Fin k, c t' * L.B.α ⟨t'.val, lt_of_lt_of_le t'.isLt L.hd⟩ q *
                L.B.u ⟨t.val, lt_of_lt_of_le t.isLt L.hd⟩ q =
                c t' * dotProduct (L.B.α ⟨t'.val, lt_of_lt_of_le t'.isLt L.hd⟩)
                  (L.B.u ⟨t.val, lt_of_lt_of_le t.isLt L.hd⟩) := by
              dsimp [dotProduct]; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro q _; ring
            rw [this, L.B.biorth]
            have hne' : (⟨t'.val, lt_of_lt_of_le t'.isLt L.hd⟩ : Fin k) ≠ ⟨t.val, lt_of_lt_of_le t.isLt L.hd⟩ :=
              fun h' => hne (Fin.ext (by simpa using congrArg Fin.val h'))
            simp [hne']
          · intro hm; exact absurd (Finset.mem_univ t) hm
        rw [heval c1, heval c2] at hdot
        exact add_left_cancel hdot
      · intro y hy
        simp only [AffSet, eqs0, Finset.mem_filter, Finset.mem_univ, true_and] at hy
        let v : Fin k → F := fun q => βout q + y q
        let c : Fin L.d → F := fun t => dotProduct v (L.B.u ⟨t.val, lt_of_lt_of_le t.isLt L.hd⟩)
        refine ⟨c, Finset.mem_univ _, ?_⟩
        funext q
        have hv : v q = ∑ t : Fin L.d, c t * L.B.α ⟨t.val, lt_of_lt_of_le t.isLt L.hd⟩ q := by
          conv_lhs => rw [L.B.expand_α v]
          dsimp only
          rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin k => i.val < L.d)]
          have hz : ∑ i ∈ Finset.univ.filter (fun i : Fin k => ¬ i.val < L.d),
              dotProduct v (L.B.u i) * L.B.α i q = 0 := by
            apply Finset.sum_eq_zero; intro i hi
            have hge : L.d ≤ i.val := by have := (Finset.mem_filter.mp hi).2; omega
            let r : Fin l := ⟨i.val - L.d, by omega⟩
            have hi_eq : (⟨L.d + r.val, by omega⟩ : Fin k) = i := Fin.ext (by dsimp [r]; omega)
            have hvr : dotProduct v (L.B.u i) = 0 := by
              rw [← hi_eq]
              have hr := hy r
              have h1 : dotProduct v (L.B.u ⟨L.d + r.val, by omega⟩) =
                  dotProduct βout (L.B.u ⟨L.d + r.val, by omega⟩) +
                    ∑ p : Fin k, L.B.u ⟨L.d + r.val, by omega⟩ p * y p := by
                simp only [v, dotProduct, add_mul, Finset.sum_add_distrib]
                congr 1; apply Finset.sum_congr rfl; intro p _; ring
              rw [h1, hr, zmod2_add_self]
            rw [hvr, zero_mul]
          rw [hz, add_zero]
          symm
          refine Finset.sum_bij (fun t _ => (⟨t.val, lt_of_lt_of_le t.isLt L.hd⟩ : Fin k)) ?_ ?_ ?_ ?_
          · intro t _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, t.isLt⟩
          · intro t1 _ t2 _ h; exact Fin.ext (by simpa using congrArg Fin.val h)
          · intro i hi; exact ⟨⟨i.val, (Finset.mem_filter.mp hi).2⟩, Finset.mem_univ _, Fin.ext rfl⟩
          · intro _ _; rfl
        dsimp [yOf]
        rw [← hv]
        dsimp [v]
        rw [← add_assoc, zmod2_add_self, zero_add]
      · intro _ _; rfl
    simpa [Fintype.card_fun, ZMod.card 2, Fintype.card_fin] using hbij

  obtain ⟨aleaves, hac_le, hapart, hasub, hasem⟩ :=
    circuit_affine_partition k L.prog.gates L.prog.rb L.prog.leg l eqs0
  let q := L.prog.gates.countP isPaid
  let j' := m - (l + q)
  have hS_eq : (∑ p ∈ Sset, chi (dotProduct βout p.1 + L.prog.val p.2 ywOut + dotProduct p.1 p.2 + g p.2)) =
      (2 : ℤ) ^ l * ∑ y ∈ AffSet eqs0, chi (Qfull y + g y) := by
    rw [hSset_bij]
    simp_rw [hinner]
    rw [← Finset.sum_filter, Finset.mul_sum]
    congr 1; ext y; simp
  have hA0_bound : 4 ^ j' * (∑ y ∈ AffSet eqs0, chi (Qfull y + g y)).natAbs ≤ (AffSet eqs0).card * 3 ^ j' := by
    have hsum_part := sum_over_partition aleaves (AffSet eqs0)
      (fun lf y => y ∈ AffSet lf.eqs) hapart (fun idx y hy => hasub _ (List.get_mem _ _) y hy)
      (fun y => chi (Qfull y + g y))
    have hcard_part := sum_over_partition aleaves (AffSet eqs0)
      (fun lf y => y ∈ AffSet lf.eqs) hapart (fun idx y hy => hasub _ (List.get_mem _ _) y hy)
      (fun _ => (1 : ℕ))
    simp only [Finset.sum_const, smul_eq_mul, mul_one] at hcard_part
    have hfilt_eq : ∀ idx : Fin aleaves.length,
        (AffSet eqs0).filter (fun y => y ∈ AffSet (aleaves.get idx).eqs) = AffSet (aleaves.get idx).eqs := by
      intro idx; ext y
      simp only [Finset.mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨hasub _ (List.get_mem _ _) y h, h⟩⟩
    simp_rw [hfilt_eq] at hsum_part hcard_part
    have hleaf_b : ∀ idx : Fin aleaves.length,
        4 ^ j' * (∑ y ∈ AffSet (aleaves.get idx).eqs, chi (Qfull y + g y)).natAbs ≤
          (AffSet (aleaves.get idx).eqs).card * 3 ^ j' := by
      intro idx
      let lf := aleaves.get idx
      have hlf_mem : lf ∈ aleaves := List.get_mem _ _
      have hc : lf.c ≤ l + q := hac_le lf hlf_mem

      let linOf (w : Fin (k + L.prog.gates.length)) (y : Fin k → F) : F :=
        (∑ i : Fin k, (lf.lin w).1 i * y i) + (lf.lin w).2
      let Qlf (y : Fin k → F) : F :=
        (∑ t : Fin L.d, linOf ⟨L.rw t, L.hrw t⟩ y *
          dotProduct (fun p => βout p + y p) (L.B.u ⟨t.val, lt_of_lt_of_le t.isLt L.hd⟩)) +
        linOf ⟨ywOut, hywOut⟩ y
      have hQlf_quad : IsQuad Qlf := by
        apply isQuad_add
        · apply isQuad_sum Finset.univ
          intro t _
          apply isQuad_mul_affine
          · exact ⟨(lf.lin ⟨L.rw t, L.hrw t⟩).1, (lf.lin ⟨L.rw t, L.hrw t⟩).2, fun _ => rfl⟩
          · refine ⟨L.B.u ⟨t.val, lt_of_lt_of_le t.isLt L.hd⟩,
              dotProduct βout (L.B.u ⟨t.val, lt_of_lt_of_le t.isLt L.hd⟩), fun y => ?_⟩
            simp only [dotProduct, add_mul, Finset.sum_add_distrib]
            rw [add_comm]
            congr 1; apply Finset.sum_congr rfl; intro p _; ring
        · exact isQuad_of_isAffine ⟨(lf.lin ⟨ywOut, hywOut⟩).1, (lf.lin ⟨ywOut, hywOut⟩).2, fun _ => rfl⟩
      have hQeq : ∑ y ∈ AffSet lf.eqs, chi (Qfull y + g y) = ∑ y ∈ AffSet lf.eqs, chi (Qlf y + g y) := by
        apply Finset.sum_congr rfl; intro y hy
        congr 2; dsimp [Qfull, Qlf, linOf]
        congr 1
        · apply Finset.sum_congr rfl; intro t _
          congr 1; exact hasem lf hlf_mem y hy ⟨L.rw t, L.hrw t⟩
        · exact hasem lf hlf_mem y hy ⟨ywOut, hywOut⟩
      rw [hQeq]
      have hcb := cubic_fiber_bound lf.c m pos Qlf hQlf_quad lf.eqs
      exact pow_three_four_mono (by dsimp [j']; omega : j' ≤ m - lf.c) _ _ hcb
    rw [hsum_part, hcard_part]
    calc 4 ^ j' * (∑ idx : Fin aleaves.length, ∑ y ∈ AffSet (aleaves.get idx).eqs, chi (Qfull y + g y)).natAbs
        ≤ 4 ^ j' * ∑ idx : Fin aleaves.length, (∑ y ∈ AffSet (aleaves.get idx).eqs, chi (Qfull y + g y)).natAbs :=
          Nat.mul_le_mul_left _ (natAbs_sum_le _ _)
      _ = ∑ idx : Fin aleaves.length, 4 ^ j' * (∑ y ∈ AffSet (aleaves.get idx).eqs, chi (Qfull y + g y)).natAbs := by
          rw [Finset.mul_sum]
      _ ≤ ∑ idx : Fin aleaves.length, (AffSet (aleaves.get idx).eqs).card * 3 ^ j' :=
          Finset.sum_le_sum (fun idx _ => hleaf_b idx)
      _ = (∑ idx : Fin aleaves.length, (AffSet (aleaves.get idx).eqs).card) * 3 ^ j' := by
          rw [Finset.sum_mul]

  have hS_j' : 4 ^ j' * (∑ p ∈ Sset, chi (dotProduct βout p.1 + L.prog.val p.2 ywOut + dotProduct p.1 p.2 + g p.2)).natAbs ≤
      2 ^ k * 3 ^ j' := by
    rw [hS_eq, Int.natAbs_mul]
    have h2l : ((2 : ℤ) ^ l).natAbs = 2 ^ l := by simp
    rw [h2l]
    have hpow : 2 ^ l * 2 ^ L.d = 2 ^ k := by rw [← pow_add, add_comm, hdl]
    calc 4 ^ j' * (2 ^ l * _) = 2 ^ l * (4 ^ j' * _) := by ring
      _ ≤ 2 ^ l * ((AffSet eqs0).card * 3 ^ j') := Nat.mul_le_mul_left _ hA0_bound
      _ = (2 ^ l * 2 ^ L.d) * 3 ^ j' := by rw [hA0_card]; ring
      _ = 2 ^ k * 3 ^ j' := by rw [hpow]
  have hbl : k - s ≤ l := by dsimp [l]; omega
  have hjj : m - (k - s + (s - k)) ≤ j' + 2 * (l - (k - s)) := by
    dsimp [j', l, q]; omega
  have hfinal := leaf_rate_mono hbl hjj hS_j'
  change 2 ^ (k - s) * 4 ^ (m - (k - s + (s - k))) *
    (∑ p ∈ Sset, chi (dotProduct βout p.1 + L.prog.val p.2 ywOut + dotProduct p.1 p.2 + g p.2)).natAbs
      ≤ Sset.card * 3 ^ (m - (k - s + (s - k)))
  rw [hSset_card, pow_add, mul_comm (2 ^ k) (2 ^ l)]
  exact hfinal

theorem upper_bound (k m s : ℕ) (pos : Fin m × Fin 3 ↪ Fin k) (C : Circuit)
    (hleg : legalCirc (2 * k) C) (hcost : circuitCost C ≤ s) :
    let g : (Fin k → F) → F := fun y => ∑ i : Fin m, y (pos (i, 0)) * y (pos (i, 1)) * y (pos (i, 2))
    let raw := (∑ x : Fin k → F, ∑ y : Fin k → F,
      if C.eval (bitsVec k x ++ bitsVec k y) = decide (dotProduct x y + g y = 1)
      then (1 : ℤ) else -1).natAbs
    let b := k - s
    let j := m - (b + (s - k))
    2 ^ b * 4 ^ j * raw ≤ 2 ^ (2 * k) * 3 ^ j := by
  classical
  dsimp only
  let g : (Fin k → F) → F := fun y => ∑ i : Fin m, y (pos (i, 0)) * y (pos (i, 1)) * y (pos (i, 2))
  let b := k - s
  let j := m - (b + (s - k))
  have hrb : ∀ idx < C.gates.length, ∀ i ∈ (C.gates.getD idx ⟨.or, []⟩).inputs, i < 2 * k + idx :=
    hleg.1
  obtain ⟨leaves, hLcost, hpart, hsem⟩ := row_leaf_partition k C.gates hrb hleg.2
  have hraw_eq : (∑ x : Fin k → F, ∑ y : Fin k → F,
      if C.eval (bitsVec k x ++ bitsVec k y) = decide (dotProduct x y + g y = 1)
      then (1 : ℤ) else -1) =
      ∑ p : (Fin k → F) × (Fin k → F),
        chi (b2z (C.eval (bitsVec k p.1 ++ bitsVec k p.2)) + dotProduct p.1 p.2 + g p.2) := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl; intro x _
    apply Finset.sum_congr rfl; intro y _
    rw [raw_term_eq_chi, add_assoc]
  rw [hraw_eq]
  have hpart_prod : ∀ p ∈ (Finset.univ : Finset ((Fin k → F) × (Fin k → F))),
      ∃! idx : Fin leaves.length, (leaves.get idx).InLeaf p.1 p.2 :=
    fun p _ => hpart p.1 p.2
  have hsum_part := sum_over_partition leaves Finset.univ
    (fun L (p : (Fin k → F) × (Fin k → F)) => L.InLeaf p.1 p.2) hpart_prod (fun _ _ _ => Finset.mem_univ _)
    (fun p => chi (b2z (C.eval (bitsVec k p.1 ++ bitsVec k p.2)) + dotProduct p.1 p.2 + g p.2))
  have hcard_part := sum_over_partition leaves Finset.univ
    (fun L (p : (Fin k → F) × (Fin k → F)) => L.InLeaf p.1 p.2) hpart_prod (fun _ _ _ => Finset.mem_univ _)
    (fun _ => (1 : ℕ))
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one,
    Fintype.card_prod, Fintype.card_fun, ZMod.card 2, Fintype.card_fin] at hcard_part
  have hpow2k : 2 ^ k * 2 ^ k = 2 ^ (2 * k) := by rw [← pow_add, two_mul]
  rw [hpow2k] at hcard_part
  have hleaf_b : ∀ idx : Fin leaves.length,
      2 ^ b * 4 ^ j *
        (∑ p ∈ Finset.univ.filter (fun p : (Fin k → F) × (Fin k → F) => (leaves.get idx).InLeaf p.1 p.2),
          chi (b2z (C.eval (bitsVec k p.1 ++ bitsVec k p.2)) + dotProduct p.1 p.2 + g p.2)).natAbs ≤
        (Finset.univ.filter (fun p : (Fin k → F) × (Fin k → F) => (leaves.get idx).InLeaf p.1 p.2)).card * 3 ^ j := by
    intro idx
    let L := leaves.get idx
    have hLmem : L ∈ leaves := List.get_mem _ _
    have hLc : L.d + L.prog.gates.countP isPaid ≤ s := le_trans (hLcost L hLmem) hcost
    by_cases hout : C.output < 2 * k + C.gates.length
    · let fout : Fin (2 * k + C.gates.length) := ⟨C.output, hout⟩
      have hterm_eq : ∀ p ∈ Finset.univ.filter (fun p : (Fin k → F) × (Fin k → F) => L.InLeaf p.1 p.2),
          chi (b2z (C.eval (bitsVec k p.1 ++ bitsVec k p.2)) + dotProduct p.1 p.2 + g p.2) =
          chi (dotProduct (L.beta fout) p.1 + L.prog.val p.2 (L.yw fout) + dotProduct p.1 p.2 + g p.2) := by
        intro p hp
        have hIn : L.InLeaf p.1 p.2 := (Finset.mem_filter.mp hp).2
        congr 3
        exact hsem L hLmem p.1 p.2 hIn fout
      rw [Finset.sum_congr rfl hterm_eq]
      exact row_leaf_bound pos L hLc (L.beta fout) (L.yw fout) (L.hyw fout)
    ·

      let r0 := L.prog.pushConst 0
      let L0 : RowLeaf k (2 * k + C.gates.length) :=
        { d := L.d
          hd := L.hd
          B := L.B
          prog := r0.val.1
          rw := L.rw
          hrw := fun t => by have := L.hrw t; have := r0.property.1; omega
          beta := L.beta
          yw := L.yw
          hyw := fun w => by have := L.hyw w; have := r0.property.1; omega }
      have hIn_eq : ∀ x y, L0.InLeaf x y ↔ L.InLeaf x y := by
        intro x y; simp only [RowLeaf.InLeaf, L0]
        apply forall_congr'; intro t
        rw [show r0.val.1.val y (L.rw t) = L.prog.val y (L.rw t) from
          r0.property.2.2.2.1 (bitsVec k y) (by simp [bitsVec]) (L.rw t) (L.hrw t)]
      have hfilt_eq : Finset.univ.filter (fun p : (Fin k → F) × (Fin k → F) => L.InLeaf p.1 p.2) =
          Finset.univ.filter (fun p : (Fin k → F) × (Fin k → F) => L0.InLeaf p.1 p.2) := by
        ext p; simp [hIn_eq]
      have hLc0 : L0.d + L0.prog.gates.countP isPaid ≤ s := by
        dsimp [L0]; rw [r0.property.2.2.1]; exact hLc
      have heval0 : ∀ x y, b2z (C.eval (bitsVec k x ++ bitsVec k y)) =
          dotProduct (fun _ => 0) x + L0.prog.val y r0.val.2 := by
        intro x y
        have hlen : (C.wires (bitsVec k x ++ bitsVec k y)).length = 2 * k + C.gates.length := by
          change (wireList C.gates (bitsVec k x ++ bitsVec k y)).length = _
          rw [wireList_length, List.length_append, bitsVec, bitsVec, List.length_ofFn, List.length_ofFn]
          omega
        have hge : (C.wires (bitsVec k x ++ bitsVec k y)).length ≤ C.output := by omega
        have hcf : C.eval (bitsVec k x ++ bitsVec k y) = false :=
          List.getD_eq_default _ _ hge
        rw [hcf]
        have hr0 : L0.prog.val y r0.val.2 = 0 :=
          r0.property.2.2.2.2 (bitsVec k y) (by simp [bitsVec])
        rw [hr0]; simp [b2z, dotProduct]
      rw [hfilt_eq]
      have hterm_eq : ∀ p ∈ Finset.univ.filter (fun p : (Fin k → F) × (Fin k → F) => L0.InLeaf p.1 p.2),
          chi (b2z (C.eval (bitsVec k p.1 ++ bitsVec k p.2)) + dotProduct p.1 p.2 + g p.2) =
          chi (dotProduct (fun _ => 0) p.1 + L0.prog.val p.2 r0.val.2 + dotProduct p.1 p.2 + g p.2) := by
        intro p _; rw [heval0]
      rw [Finset.sum_congr rfl hterm_eq]
      exact row_leaf_bound pos L0 hLc0 (fun _ => 0) r0.val.2 r0.property.2.1
  let Tleaf : Fin leaves.length → ℤ := fun idx =>
    ∑ p ∈ Finset.univ.filter (fun p : (Fin k → F) × (Fin k → F) => (leaves.get idx).InLeaf p.1 p.2),
      chi (b2z (C.eval (bitsVec k p.1 ++ bitsVec k p.2)) + dotProduct p.1 p.2 + g p.2)
  rw [hsum_part, hcard_part]
  calc 2 ^ b * 4 ^ j * (∑ idx : Fin leaves.length, Tleaf idx).natAbs
      ≤ 2 ^ b * 4 ^ j * ∑ idx : Fin leaves.length, (Tleaf idx).natAbs :=
        Nat.mul_le_mul_left _ (natAbs_sum_le _ _)
    _ = ∑ idx : Fin leaves.length, 2 ^ b * 4 ^ j * (Tleaf idx).natAbs := by rw [Finset.mul_sum]
    _ ≤ ∑ idx : Fin leaves.length, (Finset.univ.filter (fun p : (Fin k → F) × (Fin k → F) => (leaves.get idx).InLeaf p.1 p.2)).card * 3 ^ j :=
        Finset.sum_le_sum (fun idx _ => hleaf_b idx)
    _ = (∑ idx : Fin leaves.length, (Finset.univ.filter (fun p : (Fin k → F) × (Fin k → F) => (leaves.get idx).InLeaf p.1 p.2)).card) * 3 ^ j := by
        rw [Finset.sum_mul]

lemma sum_chi_disjoint_cubics :
    ∀ (j : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι] (pos : Fin j × Fin 3 ↪ ι),
      (4 : ℤ) ^ j * (∑ y : ι → F, chi (∑ i : Fin j, y (pos (i, 0)) * y (pos (i, 1)) * y (pos (i, 2)))) =
        (Fintype.card (ι → F) : ℤ) * (3 : ℤ) ^ j := by
  intro j
  induction j with
  | zero =>
    intro ι _ _ _
    simp [chi]
  | succ j ih =>
    intro ι _ _ pos
    let a := pos (Fin.last j, 0)
    let b := pos (Fin.last j, 1)
    let c := pos (Fin.last j, 2)
    have hab : a ≠ b := fun h => by have := pos.injective h; simp at this
    have hac : a ≠ c := fun h => by have := pos.injective h; simp at this
    have hbc : b ≠ c := fun h => by have := pos.injective h; simp at this
    let ι' := {x : ι // x ≠ a ∧ x ≠ b ∧ x ≠ c}
    let embed : (F × F × F) × (ι' → F) → (ι → F) := fun p x =>
      if h1 : x = a then p.1.1
      else if h2 : x = b then p.1.2.1
      else if h3 : x = c then p.1.2.2
      else p.2 ⟨x, h1, h2, h3⟩
    let split : (ι → F) → (F × F × F) × (ι' → F) := fun y =>
      ((y a, y b, y c), fun x => y x.1)
    let hEquiv : (ι → F) ≃ (F × F × F) × (ι' → F) :=
      { toFun := split
        invFun := embed
        left_inv := fun y => by
          funext x; dsimp [embed, split]
          split_ifs with h1 h2 h3
          · subst h1; rfl
          · subst h2; rfl
          · subst h3; rfl
          · rfl
        right_inv := fun ⟨⟨ua, ub, uc⟩, yr⟩ => by
          apply Prod.ext
          · apply Prod.ext
            · simp [embed, split]
            · apply Prod.ext
              · simp [embed, split, Ne.symm hab]
              · simp [embed, split, Ne.symm hac, Ne.symm hbc]
          · funext x; simp [embed, split, x.2.1, x.2.2.1, x.2.2.2] }
    have hcard : (Fintype.card (ι → F) : ℤ) = 8 * (Fintype.card (ι' → F) : ℤ) := by
      have hnat : Fintype.card (ι → F) = 8 * Fintype.card (ι' → F) := by
        rw [Fintype.card_congr hEquiv, Fintype.card_prod, Fintype.card_prod, Fintype.card_prod, ZMod.card 2]
      exact_mod_cast hnat
    let pos' : Fin j × Fin 3 ↪ ι' :=
      ⟨fun p => ⟨pos (p.1.castSucc, p.2), by
        refine ⟨?_, ?_, ?_⟩ <;> intro h <;> have h' := pos.injective h
        · exact Fin.castSucc_ne_last p.1 (Prod.mk.inj h').1
        · exact Fin.castSucc_ne_last p.1 (Prod.mk.inj h').1
        · exact Fin.castSucc_ne_last p.1 (Prod.mk.inj h').1⟩,
       fun p1 p2 h => by
        have h1 : pos (p1.1.castSucc, p1.2) = pos (p2.1.castSucc, p2.2) := congrArg Subtype.val h
        have h2 := pos.injective h1
        exact Prod.ext (Fin.castSucc_injective j (Prod.mk.inj h2).1) (Prod.mk.inj h2).2⟩
    have hsum_fac : (∑ y : ι → F, chi (∑ i : Fin (j + 1), y (pos (i, 0)) * y (pos (i, 1)) * y (pos (i, 2)))) =
        6 * (∑ yr : ι' → F, chi (∑ i : Fin j, yr (pos' (i, 0)) * yr (pos' (i, 1)) * yr (pos' (i, 2)))) := by
      rw [← Fintype.sum_equiv hEquiv.symm _ _ (fun _ => rfl)]
      rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
      simp_rw [Fintype.sum_prod_type]
      have hterm : ∀ ua ub uc yr,
          chi (∑ i : Fin (j + 1), embed ((ua, ub, uc), yr) (pos (i, 0)) *
            embed ((ua, ub, uc), yr) (pos (i, 1)) * embed ((ua, ub, uc), yr) (pos (i, 2))) =
          chi (ua * ub * uc) * chi (∑ i : Fin j, yr (pos' (i, 0)) * yr (pos' (i, 1)) * yr (pos' (i, 2))) := by
        intro ua ub uc yr
        rw [Fin.sum_univ_castSucc, add_comm, chi_add]
        congr 2
        · have h0 : embed ((ua, ub, uc), yr) a = ua := by simp [embed]
          have h1 : embed ((ua, ub, uc), yr) b = ub := by simp [embed, Ne.symm hab]
          have h2 : embed ((ua, ub, uc), yr) c = uc := by simp [embed, Ne.symm hac, Ne.symm hbc]
          exact congrArg₂ (· * ·) (congrArg₂ (· * ·) h0 h1) h2
        · apply Finset.sum_congr rfl; intro i _
          have hval : ∀ t : Fin 3, embed ((ua, ub, uc), yr) (pos (i.castSucc, t)) = yr (pos' (i, t)) := by
            intro t
            have hp := (pos' (i, t)).2
            have hp1 : pos (i.castSucc, t) ≠ a := hp.1
            have hp2 : pos (i.castSucc, t) ≠ b := hp.2.1
            have hp3 : pos (i.castSucc, t) ≠ c := hp.2.2
            dsimp [embed, pos']
            simp only [hp1, hp2, hp3, ↓reduceDIte]
            rfl
          rw [hval 0, hval 1, hval 2]
      dsimp [hEquiv]
      simp_rw [hterm]
      have hpull : ∀ (S : ℤ),
          (∑ ua : F, ∑ ub : F, ∑ uc : F, ∑ _yr : ι' → F, chi (ua * ub * uc) *
            chi (∑ i : Fin j, _yr (pos' (i, 0)) * _yr (pos' (i, 1)) * _yr (pos' (i, 2)))) =
          (∑ ua : F, ∑ ub : F, ∑ uc : F, chi (ua * ub * uc)) *
            ∑ yr : ι' → F, chi (∑ i : Fin j, yr (pos' (i, 0)) * yr (pos' (i, 1)) * yr (pos' (i, 2))) := by
        intro _
        simp_rw [← Finset.mul_sum]
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl; intro ua _
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl; intro ub _
        rw [Finset.sum_mul]
      rw [hpull 0, sum_chi_cubic_triple]
    rw [hsum_fac, hcard, pow_succ, pow_succ]
    have hih := ih pos'
    calc (4 : ℤ) ^ j * 4 * (6 * _) = 24 * ((4 : ℤ) ^ j * _) := by ring
      _ = 24 * ((Fintype.card (ι' → F) : ℤ) * (3 : ℤ) ^ j) := by rw [hih]
      _ = 8 * (Fintype.card (ι' → F) : ℤ) * ((3 : ℤ) ^ j * 3) := by ring

lemma exists_circuit_of_terms (k : ℕ) (term : Fin k → Option (Fin k × Fin k)) (keep : Fin k → Bool) :
    ∃ C : Circuit,
      legalCirc (2 * k) C ∧
      circuitCost C = (Finset.univ.filter (fun r : Fin k => keep r = true)).card +
        (Finset.univ.filter (fun r : Fin k => keep r = true ∧ (term r).isSome)).card ∧
      ∀ x y : Fin k → F,
        b2z (C.eval (bitsVec k x ++ bitsVec k y)) =
          ∑ r : Fin k, if keep r = true then
            (match term r with
             | none => x r * y r
             | some (p1, p2) => (x r + y p1 * y p2) * y r)
          else 0 := by

  have haux : ∀ (l : List (Fin k)),
      ∃ (P : YProg (2 * k)) (w : ℕ),
        w < 2 * k + P.gates.length ∧
        P.gates.countP isPaid =
          (l.countP (fun r => keep r)) + (l.countP (fun r => keep r && (term r).isSome)) ∧
        ∀ x y : Fin k → F,
          P.valList (bitsVec k x ++ bitsVec k y) w =
            (l.map fun r => if keep r = true then
              (match term r with
               | none => x r * y r
               | some (p1, p2) => (x r + y p1 * y p2) * y r)
            else 0).sum := by
    intro l
    induction l with
    | nil =>
      let r0 := (YProg.empty (2 * k)).pushConst 0
      refine ⟨r0.val.1, r0.val.2, r0.property.2.1, ?_, fun x y => ?_⟩
      · rw [r0.property.2.2.1]; simp [YProg.empty]
      · have hinp : (bitsVec k x ++ bitsVec k y).length = 2 * k := by simp [bitsVec]; omega
        simpa using r0.property.2.2.2.2 (bitsVec k x ++ bitsVec k y) hinp
    | cons r rest ih =>
      obtain ⟨P, wRest, hwRest, hcostP, hvalP⟩ := ih
      have hinp_len : ∀ x y : Fin k → F, (bitsVec k x ++ bitsVec k y).length = 2 * k := fun x y => by
        simp [bitsVec]; omega
      have hx_wire : ∀ (x y : Fin k → F) (q : Fin k) (P' : YProg (2 * k)),
          P'.valList (bitsVec k x ++ bitsVec k y) q.val = x q := by
        intro x y q P'
        dsimp [YProg.valList]
        rw [wireList_getD_lt P'.gates _ q.val (by rw [hinp_len]; omega)]
        rw [getD_append_lt (by simp [bitsVec])]
        dsimp [bitsVec]
        rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn, b2z_decide_eq_one]
      have hy_wire : ∀ (x y : Fin k → F) (q : Fin k) (P' : YProg (2 * k)),
          P'.valList (bitsVec k x ++ bitsVec k y) (k + q.val) = y q := by
        intro x y q P'
        dsimp [YProg.valList]
        rw [wireList_getD_lt P'.gates _ (k + q.val) (by rw [hinp_len]; omega)]
        have hlt : k + q.val < (bitsVec k x ++ bitsVec k y).length := by rw [hinp_len]; omega
        rw [List.getD_eq_getElem _ _ hlt, List.getElem_append_right (by simp [bitsVec])]
        simp only [bitsVec, List.length_ofFn, Nat.add_sub_cancel_left, List.getElem_ofFn, b2z_decide_eq_one]
      cases hkeep : keep r
      · refine ⟨P, wRest, hwRest, ?_, fun x y => ?_⟩
        · simp [hkeep, hcostP]
        · simp [hkeep, hvalP]
      · cases hterm : term r with
        | none =>
          let rAnd := P.pushPaid .and (Or.inl rfl) r.val (k + r.val) (by omega) (by omega)
          let rXor := rAnd.val.1.pushXor rAnd.val.2 wRest rAnd.property.2.1 (by have := rAnd.property.1; omega)
          refine ⟨rXor.val.1, rXor.val.2, rXor.property.2.1, ?_, fun x y => ?_⟩
          · rw [rXor.property.2.2.1, rAnd.property.2.2.1, hcostP]
            simp [hkeep, hterm]; omega
          · rw [rXor.property.2.2.2.2 _ (hinp_len x y),
                rAnd.property.2.2.2.2 _ (hinp_len x y),
                rAnd.property.2.2.2.1 _ (hinp_len x y) wRest hwRest,
                hx_wire x y r P, hy_wire x y r P, hvalP x y]
            simp [hkeep, hterm]
        | some pq =>
          let p1 := pq.1; let p2 := pq.2
          let r1 := P.pushPaid .and (Or.inl rfl) (k + p1.val) (k + p2.val) (by omega) (by omega)
          let r2 := r1.val.1.pushXor r.val r1.val.2 (by omega) r1.property.2.1
          let r3 := r2.val.1.pushPaid .and (Or.inl rfl) r2.val.2 (k + r.val) r2.property.2.1 (by omega)
          have hwRest3 : wRest < 2 * k + r3.val.1.gates.length := by
            have := r1.property.1; have := r2.property.1; have := r3.property.1; omega
          let r4 := r3.val.1.pushXor r3.val.2 wRest r3.property.2.1 hwRest3
          refine ⟨r4.val.1, r4.val.2, r4.property.2.1, ?_, fun x y => ?_⟩
          · rw [r4.property.2.2.1, r3.property.2.2.1, r2.property.2.2.1, r1.property.2.2.1, hcostP]
            simp [hkeep, hterm]; omega
          · have h1 := r1.property.1; have h2 := r2.property.1; have h3 := r3.property.1
            rw [r4.property.2.2.2.2 _ (hinp_len x y),
                r3.property.2.2.2.2 _ (hinp_len x y),
                r3.property.2.2.2.1 _ (hinp_len x y) wRest (by omega),
                r2.property.2.2.2.1 _ (hinp_len x y) wRest (by omega),
                r1.property.2.2.2.1 _ (hinp_len x y) wRest hwRest,
                r2.property.2.2.2.2 _ (hinp_len x y),
                r1.property.2.2.2.2 _ (hinp_len x y),
                hx_wire x y r r1.val.1, hy_wire x y r r2.val.1,
                hy_wire x y p1 P, hy_wire x y p2 P, hvalP x y]
            simp [hkeep, hterm, p1, p2]
  obtain ⟨P, w, _, hcostP, hvalP⟩ := haux (List.finRange k)
  refine ⟨⟨P.gates, w⟩, ⟨P.rb, P.leg⟩, ?_, fun x y => ?_⟩
  · dsimp [circuitCost]
    rw [hcostP]
    have hcnt : ∀ (p : Fin k → Bool),
        (List.finRange k).countP p = (Finset.univ.filter (fun r : Fin k => p r = true)).card := by
      intro p
      rw [List.countP_eq_length_filter]
      have hnd : (List.finRange k).Nodup := List.nodup_finRange k
      have h1 := List.toFinset_card_of_nodup (hnd.filter p)
      rw [← h1]
      congr 1; ext r; simp
    rw [hcnt, hcnt]
    simp [Bool.and_eq_true]
  · have h := hvalP x y
    change b2z ((wireList P.gates (bitsVec k x ++ bitsVec k y)).getD w false) = _
    dsimp [YProg.valList] at h
    rw [h, ← Fin.sum_univ_def]

theorem exists_opt_circuit (k m s : ℕ) (pos : Fin m × Fin 3 ↪ Fin k) :
    let g : (Fin k → F) → F := fun y => ∑ i : Fin m, y (pos (i, 0)) * y (pos (i, 1)) * y (pos (i, 2))
    let raw := fun (C : Circuit) => (∑ x : Fin k → F, ∑ y : Fin k → F,
      if C.eval (bitsVec k x ++ bitsVec k y) = decide (dotProduct x y + g y = 1)
      then (1 : ℤ) else -1).natAbs
    let b := k - s
    let j := m - (b + (s - k))
    ∃ C : Circuit, legalCirc (2 * k) C ∧ circuitCost C ≤ s ∧
      2 ^ b * 4 ^ j * raw C = 2 ^ (2 * k) * 3 ^ j := by
  classical
  dsimp only
  let g : (Fin k → F) → F := fun y => ∑ i : Fin m, y (pos (i, 0)) * y (pos (i, 1)) * y (pos (i, 2))
  let b := k - s
  let j := m - (b + (s - k))
  by_cases hsk : s ≤ k
  ·
    have hsm : s - k = 0 := by omega
    have hj_eq : j = m - b := by dsimp [j]; omega
    let S0 : Finset (Fin k) := (Finset.univ.filter (fun i : Fin m => i.val < min b m)).image (fun i => pos (i, 0))
    have hS0_card : S0.card = min b m := by
      rw [Finset.card_image_of_injective _ (fun i1 i2 h => congrArg Prod.fst (pos.injective h))]
      have hcard : (Finset.univ.filter (fun i : Fin m => i.val < min b m)).card = min b m := by
        have hbij : ∑ _i ∈ Finset.univ.filter (fun i : Fin m => i.val < min b m), (1 : ℕ) =
            ∑ _r : Fin (min b m), (1 : ℕ) := by
          symm
          refine Finset.sum_bij (fun r _ => (⟨r.val, by omega⟩ : Fin m)) ?_ ?_ ?_ ?_
          · intro r _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, r.isLt⟩
          · intro r1 _ r2 _ h; exact Fin.ext (by simpa using congrArg Fin.val h)
          · intro i hi; exact ⟨⟨i.val, (Finset.mem_filter.mp hi).2⟩, Finset.mem_univ _, Fin.ext rfl⟩
          · intro _ _; rfl
        simpa using hbij
      exact hcard
    have hrem_card : b - min b m ≤ (Finset.univ \ S0).card := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ S0), Finset.card_univ, Fintype.card_fin, hS0_card]
      dsimp [b]; omega
    obtain ⟨S1, hS1_sub, hS1_card⟩ := Finset.exists_subset_card_eq hrem_card
    let omitSet : Finset (Fin k) := S0 ∪ S1
    have hdisj : Disjoint S0 S1 :=
      Finset.disjoint_left.mpr (fun r hr0 hr1 => (Finset.mem_sdiff.mp (hS1_sub hr1)).2 hr0)
    have homit_card : omitSet.card = b := by
      rw [Finset.card_union_of_disjoint hdisj, hS0_card, hS1_card]; omega
    have hS1_empty_if : b ≤ m → S1 = ∅ := by
      intro hbm
      have : S1.card = 0 := by rw [hS1_card]; omega
      exact Finset.card_eq_zero.mp this
    obtain ⟨C, hlegC, hcostC, hevalC⟩ :=
      exists_circuit_of_terms k (fun _ => none) (fun r => decide (r ∉ omitSet))
    refine ⟨C, hlegC, ?_, ?_⟩
    · rw [hcostC]
      have h1 : (Finset.univ.filter (fun r : Fin k => decide (r ∉ omitSet) = true ∧ (Option.none (α := Fin k × Fin k)).isSome)).card = 0 := by
        simp
      have h2 : (Finset.univ.filter (fun r : Fin k => decide (r ∉ omitSet) = true)).card = k - b := by
        have hcomp : Finset.univ.filter (fun r : Fin k => decide (r ∉ omitSet) = true) = Finset.univ \ omitSet := by
          ext r; simp
        rw [hcomp, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin, homit_card]
      rw [h1, h2, add_zero]; dsimp [b]; omega
    ·
      have hdiff : ∀ x y : Fin k → F,
          b2z (C.eval (bitsVec k x ++ bitsVec k y)) + dotProduct x y + g y =
          (∑ r ∈ omitSet, x r * y r) + g y := by
        intro x y
        rw [hevalC x y]
        dsimp [dotProduct]
        have hsum_all : (∑ r : Fin k, x r * y r) =
            (∑ r ∈ omitSet, x r * y r) + (∑ r ∈ Finset.univ \ omitSet, x r * y r) := by
          rw [← Finset.sum_add_sum_compl omitSet (fun r => x r * y r)]
          rfl
        have hsum_keep : (∑ r : Fin k, if decide (r ∉ omitSet) = true then x r * y r else 0) =
            ∑ r ∈ Finset.univ \ omitSet, x r * y r := by
          rw [← Finset.sum_filter]
          congr 1; ext r; simp
        rw [hsum_keep, hsum_all]
        have : (∑ r ∈ Finset.univ \ omitSet, x r * y r) +
            ((∑ r ∈ omitSet, x r * y r) + ∑ r ∈ Finset.univ \ omitSet, x r * y r) =
            (∑ r ∈ omitSet, x r * y r) +
            ((∑ r ∈ Finset.univ \ omitSet, x r * y r) + ∑ r ∈ Finset.univ \ omitSet, x r * y r) := by ring
        rw [this, zmod2_add_self, add_zero]
      have hraw_sum : (∑ x : Fin k → F, ∑ y : Fin k → F,
          if C.eval (bitsVec k x ++ bitsVec k y) = decide (dotProduct x y + g y = 1)
          then (1 : ℤ) else -1) =
          (2 : ℤ) ^ k * ∑ y ∈ Finset.univ.filter (fun y : Fin k → F => ∀ r ∈ omitSet, y r = 0), chi (g y) := by
        have h1 : ∀ x y, (if C.eval (bitsVec k x ++ bitsVec k y) = decide (dotProduct x y + g y = 1) then (1 : ℤ) else -1) =
            chi ((∑ r ∈ omitSet, x r * y r) + g y) := by
          intro x y; rw [raw_term_eq_chi, ← add_assoc, hdiff]
        simp_rw [h1]
        rw [Finset.sum_comm, Finset.mul_sum]
        have hinner_x : ∀ y : Fin k → F,
            (∑ x : Fin k → F, chi ((∑ r ∈ omitSet, x r * y r) + g y)) =
            if ∀ r ∈ omitSet, y r = 0 then (2 : ℤ) ^ k * chi (g y) else 0 := by
          intro y
          simp_rw [chi_add, ← Finset.sum_mul]
          have hsum_x : (∑ x : Fin k → F, chi (∑ r ∈ omitSet, x r * y r)) =
              ∑ x : Fin k → F, chi (∑ r : Fin k, x r * (if r ∈ omitSet then y r else 0)) := by
            apply Finset.sum_congr rfl; intro x _
            congr 1
            have hf : ∀ r : Fin k, x r * (if r ∈ omitSet then y r else 0) = if r ∈ omitSet then x r * y r else 0 :=
              fun r => by split_ifs <;> ring
            simp_rw [hf, ← Finset.sum_filter]
            congr 1; ext r; simp
          rw [hsum_x, sum_chi_dot_fin]
          have hcond : (∀ r : Fin k, (if r ∈ omitSet then y r else 0) = 0) ↔ ∀ r ∈ omitSet, y r = 0 := by
            constructor
            · intro h r hr; simpa [hr] using h r
            · intro h r; by_cases hr : r ∈ omitSet <;> simp [hr, h]
          by_cases hy : ∀ r ∈ omitSet, y r = 0
          · rw [if_pos hy, if_pos (hcond.mpr hy)]
          · rw [if_neg hy, if_neg (fun h => hy (hcond.mp h)), zero_mul]
        simp_rw [hinner_x]
        rw [← Finset.sum_filter]

      let ιK := {r : Fin k // r ∉ omitSet}
      have hcard_ιK : Fintype.card ιK = k - b := by
        have h1 : Fintype.card ιK = (Finset.univ \ omitSet).card := by
          rw [Fintype.card_subtype]
          congr 1; ext r; simp
        rw [h1, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin, homit_card]
      have hcard_funK : Fintype.card (ιK → F) = 2 ^ (k - b) := by
        rw [Fintype.card_fun, ZMod.card 2, hcard_ιK]
      let posK : Fin j × Fin 3 ↪ ιK :=
        ⟨fun p => ⟨pos (⟨b + p.1.val, by dsimp [j] at p; omega⟩, p.2), by
          intro hmem
          have hbm : b < m := by have := p.1.isLt; omega
          have hS1e : S1 = ∅ := hS1_empty_if (le_of_lt hbm)
          have hmem0 : pos (⟨b + p.1.val, by omega⟩, p.2) ∈ S0 := by
            simpa [omitSet, hS1e] using hmem
          obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp hmem0
          have hilt : i.val < min b m := (Finset.mem_filter.mp hi).2
          have hfst : i.val = b + p.1.val := congrArg (fun q => q.1.val) (pos.injective heq)
          omega⟩,
         fun p1 p2 h => by
          have h1 := pos.injective (congrArg Subtype.val h)
          have hf : b + p1.1.val = b + p2.1.val := congrArg (fun q => q.1.val) h1
          exact Prod.ext (Fin.ext (by omega)) (Prod.mk.inj h1).2⟩
      let liftK (z : ιK → F) : Fin k → F := fun r => if hr : r ∈ omitSet then 0 else z ⟨r, hr⟩
      have hsum_y : (∑ y ∈ Finset.univ.filter (fun y : Fin k → F => ∀ r ∈ omitSet, y r = 0), chi (g y)) =
          ∑ z : ιK → F, chi (∑ i : Fin j, z (posK (i, 0)) * z (posK (i, 1)) * z (posK (i, 2))) := by
        symm
        refine Finset.sum_bij (fun z _ => liftK z) ?_ ?_ ?_ ?_
        · intro z _
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          intro r hr; simp [liftK, hr]
        · intro z1 _ z2 _ h
          funext x; have := congrFun h x.1; simpa [liftK, x.2] using this
        · intro y hy
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
          refine ⟨fun x => y x.1, Finset.mem_univ _, ?_⟩
          funext r; dsimp [liftK]
          split_ifs with hr
          · exact (hy r hr).symm
          · rfl
        · intro z _
          congr 1; dsimp [g]
          rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin m => i.val < min b m)]
          have hz_low : ∑ i ∈ Finset.univ.filter (fun i : Fin m => i.val < min b m),
              liftK z (pos (i, 0)) * liftK z (pos (i, 1)) * liftK z (pos (i, 2)) = 0 := by
            apply Finset.sum_eq_zero; intro i hi
            have hmem : pos (i, 0) ∈ omitSet :=
              Finset.mem_union_left S1 (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
            simp [liftK, hmem]
          rw [hz_low, zero_add]
          refine Finset.sum_bij (fun (i : Fin j) _ => (⟨b + i.val, by have := i.isLt; dsimp [j] at this; omega⟩ : Fin m)) ?_ ?_ ?_ ?_
          · intro i _
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by have := i.isLt; dsimp [j] at this; dsimp; omega⟩
          · intro i1 _ i2 _ h; exact Fin.ext (by have := congrArg Fin.val h; dsimp at this; omega)
          · intro i hi
            have hge : min b m ≤ i.val := by have := (Finset.mem_filter.mp hi).2; omega
            have hbm : b ≤ i.val := by have := i.isLt; omega
            refine ⟨⟨i.val - b, by have := i.isLt; dsimp [j]; omega⟩, Finset.mem_univ _, Fin.ext (by dsimp; omega)⟩
          · intro i _
            have hval : ∀ t : Fin 3, z (posK (i, t)) = liftK z (pos (⟨b + i.val, by have := i.isLt; dsimp [j] at this; omega⟩, t)) := by
              intro t
              have hnot : pos (⟨b + i.val, by have := i.isLt; dsimp [j] at this; omega⟩, t) ∉ omitSet := (posK (i, t)).2
              dsimp [liftK, posK]
              simp only [hnot, ↓reduceDIte]
              rfl
            rw [hval 0, hval 1, hval 2]
      have hcub := sum_chi_disjoint_cubics j posK
      rw [hcard_funK] at hcub
      have hraw_val : (2 : ℤ) ^ b * (4 : ℤ) ^ j *
          (∑ x : Fin k → F, ∑ y : Fin k → F,
            if C.eval (bitsVec k x ++ bitsVec k y) = decide (dotProduct x y + g y = 1)
            then (1 : ℤ) else -1) = (2 : ℤ) ^ (2 * k) * (3 : ℤ) ^ j := by
        rw [hraw_sum, hsum_y]
        have hbk : b + (k - b) = k := Nat.add_sub_of_le (by dsimp [b]; omega)
        calc (2 : ℤ) ^ b * (4 : ℤ) ^ j * ((2 : ℤ) ^ k * _)
            = (2 : ℤ) ^ b * (2 : ℤ) ^ k * ((4 : ℤ) ^ j * _) := by ring
          _ = (2 : ℤ) ^ b * (2 : ℤ) ^ k * (((2 ^ (k - b) : ℕ) : ℤ) * (3 : ℤ) ^ j) := by rw [hcub]
          _ = ((2 : ℤ) ^ b * (2 : ℤ) ^ (k - b)) * (2 : ℤ) ^ k * (3 : ℤ) ^ j := by push_cast; ring
          _ = (2 : ℤ) ^ (b + (k - b)) * (2 : ℤ) ^ k * (3 : ℤ) ^ j := by rw [pow_add]
          _ = (2 : ℤ) ^ (2 * k) * (3 : ℤ) ^ j := by rw [hbk, ← pow_add, two_mul]
      have hnat := congrArg Int.natAbs hraw_val
      simp only [Int.natAbs_mul, Int.natAbs_pow] at hnat
      simpa using hnat
  ·
    have hb0 : b = 0 := by dsimp [b]; omega
    let d := min (s - k) m
    have hj_eq : j = m - d := by dsimp [j, d]; omega
    let term : Fin k → Option (Fin k × Fin k) := fun r =>
      if h : ∃ i : Fin m, i.val < d ∧ pos (i, 0) = r then
        let i := Classical.choose h
        some (pos (i, 1), pos (i, 2))
      else none
    obtain ⟨C, hlegC, hcostC, hevalC⟩ := exists_circuit_of_terms k term (fun _ => true)
    refine ⟨C, hlegC, ?_, ?_⟩
    · rw [hcostC]
      have h1 : (Finset.univ.filter (fun _ : Fin k => true = true)).card = k := by simp
      have h2 : (Finset.univ.filter (fun r : Fin k => true = true ∧ (term r).isSome)).card = d := by
        have heq : Finset.univ.filter (fun r : Fin k => true = true ∧ (term r).isSome) =
            (Finset.univ.filter (fun i : Fin m => i.val < d)).image (fun i => pos (i, 0)) := by
          ext r
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, term]
          constructor
          · intro h
            by_cases hex : ∃ i : Fin m, i.val < d ∧ pos (i, 0) = r
            · obtain ⟨i, hi, hr⟩ := hex; exact ⟨i, hi, hr⟩
            · simp [hex] at h
          · rintro ⟨i, hi, hr⟩
            have hex : ∃ i : Fin m, i.val < d ∧ pos (i, 0) = r := ⟨i, hi, hr⟩
            simp [hex]
        rw [heq, Finset.card_image_of_injective _ (fun i1 i2 h => congrArg Prod.fst (pos.injective h))]
        have hbij : ∑ _i ∈ Finset.univ.filter (fun i : Fin m => i.val < d), (1 : ℕ) =
            ∑ _r : Fin d, (1 : ℕ) := by
          symm
          refine Finset.sum_bij (fun r _ => (⟨r.val, by dsimp [d] at r; omega⟩ : Fin m)) ?_ ?_ ?_ ?_
          · intro r _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, r.isLt⟩
          · intro r1 _ r2 _ h; exact Fin.ext (by simpa using congrArg Fin.val h)
          · intro i hi; exact ⟨⟨i.val, (Finset.mem_filter.mp hi).2⟩, Finset.mem_univ _, Fin.ext rfl⟩
          · intro _ _; rfl
        simpa using hbij
      rw [h1, h2]; dsimp [d]; omega
    ·
      have heval_simp : ∀ x y : Fin k → F,
          b2z (C.eval (bitsVec k x ++ bitsVec k y)) =
          dotProduct x y + ∑ i ∈ Finset.univ.filter (fun i : Fin m => i.val < d),
            y (pos (i, 0)) * y (pos (i, 1)) * y (pos (i, 2)) := by
        intro x y
        rw [hevalC x y]
        have hterm_split : ∀ r : Fin k,
            (if true = true then match term r with
              | none => x r * y r
              | some (p1, p2) => (x r + y p1 * y p2) * y r else 0) =
            x r * y r + (if h : ∃ i : Fin m, i.val < d ∧ pos (i, 0) = r then
              let i := Classical.choose h
              y (pos (i, 0)) * y (pos (i, 1)) * y (pos (i, 2)) else 0) := by
          intro r
          simp only [↓reduceIte, term]
          split_ifs with h
          · have hr : pos (Classical.choose h, 0) = r := (Classical.choose_spec h).2
            rw [hr]; ring
          · simp
        rw [Finset.sum_congr rfl (fun r _ => hterm_split r), Finset.sum_add_distrib]
        congr 1
        rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun r : Fin k => ∃ i : Fin m, i.val < d ∧ pos (i, 0) = r)]
        have hzero : ∑ r ∈ Finset.univ.filter (fun r : Fin k => ¬ ∃ i : Fin m, i.val < d ∧ pos (i, 0) = r),
            (if h : ∃ i : Fin m, i.val < d ∧ pos (i, 0) = r then
              let i := Classical.choose h
              y (pos (i, 0)) * y (pos (i, 1)) * y (pos (i, 2)) else 0) = 0 := by
          apply Finset.sum_eq_zero; intro r hr
          have hnot := (Finset.mem_filter.mp hr).2
          simp only [hnot, ↓reduceDIte]
        rw [hzero, add_zero]
        symm
        refine Finset.sum_bij (fun i _ => pos (i, 0)) ?_ ?_ ?_ ?_
        · intro i hi
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨i, (Finset.mem_filter.mp hi).2, rfl⟩⟩
        · intro i1 _ i2 _ h; exact (Prod.mk.inj (pos.injective h)).1
        · intro r hr
          obtain ⟨i, hi, hpos⟩ := (Finset.mem_filter.mp hr).2
          exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, hpos⟩
        · intro i hi
          have hex : ∃ i' : Fin m, i'.val < d ∧ pos (i', 0) = pos (i, 0) :=
            ⟨i, (Finset.mem_filter.mp hi).2, rfl⟩
          simp only [hex, ↓reduceDIte]
          have hch : Classical.choose hex = i :=
            (Prod.mk.inj (pos.injective (Classical.choose_spec hex).2)).1
          rw [hch]
      let posJ : Fin j × Fin 3 ↪ Fin k :=
        ⟨fun p => pos (⟨d + p.1.val, by have := p.1.isLt; dsimp [j, d] at this ⊢; omega⟩, p.2),
         fun p1 p2 h => by
          have h1 := pos.injective h
          have hf : d + p1.1.val = d + p2.1.val := congrArg (fun q => q.1.val) h1
          exact Prod.ext (Fin.ext (by omega)) (Prod.mk.inj h1).2⟩
      have hdiff : ∀ x y : Fin k → F,
          b2z (C.eval (bitsVec k x ++ bitsVec k y)) + dotProduct x y + g y =
          ∑ i : Fin j, y (posJ (i, 0)) * y (posJ (i, 1)) * y (posJ (i, 2)) := by
        intro x y
        rw [heval_simp x y]
        dsimp [g]
        rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin m => i.val < d)]
        have hcancel : (dotProduct x y + ∑ i ∈ Finset.univ.filter (fun i : Fin m => i.val < d),
            y (pos (i, 0)) * y (pos (i, 1)) * y (pos (i, 2))) + dotProduct x y +
            ((∑ i ∈ Finset.univ.filter (fun i : Fin m => i.val < d),
              y (pos (i, 0)) * y (pos (i, 1)) * y (pos (i, 2))) +
            ∑ i ∈ Finset.univ.filter (fun i : Fin m => ¬ i.val < d),
              y (pos (i, 0)) * y (pos (i, 1)) * y (pos (i, 2))) =
            ∑ i ∈ Finset.univ.filter (fun i : Fin m => ¬ i.val < d),
              y (pos (i, 0)) * y (pos (i, 1)) * y (pos (i, 2)) := by
          let A := dotProduct x y
          let B := ∑ i ∈ Finset.univ.filter (fun i : Fin m => i.val < d),
              y (pos (i, 0)) * y (pos (i, 1)) * y (pos (i, 2))
          let D := ∑ i ∈ Finset.univ.filter (fun i : Fin m => ¬ i.val < d),
              y (pos (i, 0)) * y (pos (i, 1)) * y (pos (i, 2))
          calc (A + B) + A + (B + D) = (A + A) + (B + B) + D := by ring
            _ = D := by rw [zmod2_add_self, zmod2_add_self, zero_add, zero_add]
        rw [hcancel]
        symm
        refine Finset.sum_bij (fun (i : Fin j) _ => (⟨d + i.val, by have := i.isLt; dsimp [j, d] at this ⊢; omega⟩ : Fin m)) ?_ ?_ ?_ ?_
        · intro i _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp; omega⟩
        · intro i1 _ i2 _ h; exact Fin.ext (by have := congrArg Fin.val h; dsimp at this; omega)
        · intro i hi
          have hge : d ≤ i.val := by have := (Finset.mem_filter.mp hi).2; omega
          exact ⟨⟨i.val - d, by have := i.isLt; dsimp [j, d]; omega⟩, Finset.mem_univ _, Fin.ext (by dsimp; omega)⟩
        · intro i _; rfl
      have hcub := sum_chi_disjoint_cubics j posJ
      have hcard_fk : Fintype.card (Fin k → F) = 2 ^ k := by
        rw [Fintype.card_fun, ZMod.card 2, Fintype.card_fin]
      rw [hcard_fk] at hcub
      have hraw_val : (2 : ℤ) ^ b * (4 : ℤ) ^ j *
          (∑ x : Fin k → F, ∑ y : Fin k → F,
            if C.eval (bitsVec k x ++ bitsVec k y) = decide (dotProduct x y + g y = 1)
            then (1 : ℤ) else -1) = (2 : ℤ) ^ (2 * k) * (3 : ℤ) ^ j := by
        have h1 : ∀ x y, (if C.eval (bitsVec k x ++ bitsVec k y) = decide (dotProduct x y + g y = 1) then (1 : ℤ) else -1) =
            chi (∑ i : Fin j, y (posJ (i, 0)) * y (posJ (i, 1)) * y (posJ (i, 2))) := by
          intro x y; rw [raw_term_eq_chi, ← add_assoc, hdiff]
        simp_rw [h1]
        rw [Finset.sum_const, Finset.card_univ, hcard_fk, nsmul_eq_mul, hb0, pow_zero, one_mul]
        calc (4 : ℤ) ^ j * (((2 ^ k : ℕ) : ℤ) * _)
            = (2 : ℤ) ^ k * ((4 : ℤ) ^ j * _) := by push_cast; ring
          _ = (2 : ℤ) ^ k * (((2 ^ k : ℕ) : ℤ) * (3 : ℤ) ^ j) := by rw [hcub]
          _ = (2 : ℤ) ^ (2 * k) * (3 : ℤ) ^ j := by push_cast; rw [← mul_assoc, ← pow_add, two_mul]
      have hnat := congrArg Int.natAbs hraw_val
      simp only [Int.natAbs_mul, Int.natAbs_pow] at hnat
      simpa using hnat

end

end PEqualNP.Outside.L_meta_29766_aux

theorem PEqualNP.Outside.L_meta_29766 : (∀ (k m s : ℕ),
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
  ∀ pos : (Fin m × Fin 3) ↪ Fin k,
    let g := fun (y : V) => ∑ i : Fin m, y (pos (i,0)) * y (pos (i,1)) * y (pos (i,2))
    let raw := fun (C : Circ) => (∑ x : V, ∑ y : V,
      if C.eval (bits k x ++ bits k y) = decide (dotProduct x y + g y = 1)
      then (1 : ℤ) else -1).natAbs
    let b := k-s
    let j := m-(b+(s-k))
    (∀ C : Circ, legal (2*k) C → cost C ≤ s →
      2^b*4^j*raw C ≤ 2^(2*k)*3^j) ∧
    (∃ C : Circ, legal (2*k) C ∧ cost C ≤ s ∧
      2^b*4^j*raw C = 2^(2*k)*3^j)) := by
  intro k m s Circ F legal cost bits V pos g raw b j
  exact ⟨fun C hleg hcost => PEqualNP.Outside.L_meta_29766_aux.upper_bound k m s pos C hleg hcost,
         PEqualNP.Outside.L_meta_29766_aux.exists_opt_circuit k m s pos⟩
