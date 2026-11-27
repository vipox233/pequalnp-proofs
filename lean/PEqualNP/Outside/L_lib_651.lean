import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_651_aux

private def disc {n : ℕ} (F : Fin n → Fin n → Bool) (a b : Fin n) : Prop :=
  F a b ≠ F b a

private lemma disc_symm {n : ℕ} (F : Fin n → Fin n → Bool) {a b : Fin n} :
    disc F a b ↔ disc F b a := by
  unfold disc
  exact ne_comm

private lemma disc_irrefl {n : ℕ} (F : Fin n → Fin n → Bool) (a : Fin n) :
    ¬ disc F a a := by
  unfold disc
  exact fun h => h rfl

private def degIn {n : ℕ} (F : Fin n → Fin n → Bool) (S : Finset (Fin n)) (v : Fin n) : ℕ :=
  (S.filter (fun u => F v u ≠ F u v)).card

private def dirEdges {n : ℕ} (F : Fin n → Fin n → Bool) (S : Finset (Fin n)) : ℕ :=
  ((S ×ˢ S).filter (fun z => F z.1 z.2 ≠ F z.2 z.1)).card

private lemma dirEdges_eq_sum_deg {n : ℕ} (F : Fin n → Fin n → Bool) (S : Finset (Fin n)) :
    dirEdges F S = ∑ v ∈ S, degIn F S v := by
  unfold dirEdges degIn
  rw [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]

private lemma dirEdges_erase {n : ℕ} (F : Fin n → Fin n → Bool) (S : Finset (Fin n))
    (v : Fin n) (hv : v ∈ S) :
    dirEdges F (S.erase v) + 2 * degIn F S v = dirEdges F S := by
  rw [dirEdges_eq_sum_deg, dirEdges_eq_sum_deg]
  rw [← Finset.add_sum_erase S (degIn F S) hv]
  have hterm : ∀ u ∈ S.erase v,
      degIn F (S.erase v) u + (if F v u ≠ F u v then 1 else 0) = degIn F S u := by
    intro u hu
    unfold degIn
    have hflt : (S.erase v).filter (fun w => F u w ≠ F w u) =
        (S.filter (fun w => F u w ≠ F w u)).erase v := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_erase]
      tauto
    rw [hflt]
    by_cases hd : F v u ≠ F u v
    · have hmem : v ∈ S.filter (fun w => F u w ≠ F w u) :=
        Finset.mem_filter.mpr ⟨hv, hd.symm⟩
      rw [if_pos hd]
      have hpos : 1 ≤ (S.filter (fun w => F u w ≠ F w u)).card :=
        Finset.card_pos.mpr ⟨v, hmem⟩
      rw [Finset.card_erase_of_mem hmem]
      omega
    · have hnot : v ∉ S.filter (fun w => F u w ≠ F w u) := by
        intro hm
        exact hd (Finset.mem_filter.mp hm).2.symm
      rw [if_neg hd, add_zero, Finset.erase_eq_of_notMem hnot]
  have hsum_er :
      (∑ u ∈ S.erase v, (degIn F (S.erase v) u + if F v u ≠ F u v then 1 else 0)) =
        ∑ u ∈ S.erase v, degIn F S u :=
    Finset.sum_congr rfl hterm
  rw [Finset.sum_add_distrib] at hsum_er
  have hdeg_eq : (∑ u ∈ S.erase v, if F v u ≠ F u v then 1 else 0) = degIn F S v := by
    unfold degIn
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
    congr 1
    ext u
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · exact fun h => ⟨h.1.2, h.2⟩
    · rintro ⟨hu, hd⟩
      refine ⟨⟨?_, hu⟩, hd⟩
      intro hEq; subst hEq; exact hd rfl
  omega

private lemma exists_max_deg {n : ℕ} (F : Fin n → Fin n → Bool) (S : Finset (Fin n))
    (hne : S.Nonempty) :
    ∃ v ∈ S, dirEdges F S ≤ S.card * degIn F S v := by
  obtain ⟨v, hv, hmax⟩ := Finset.exists_max_image S (degIn F S) hne
  refine ⟨v, hv, ?_⟩
  rw [dirEdges_eq_sum_deg]
  calc
    ∑ u ∈ S, degIn F S u ≤ ∑ _u ∈ S, degIn F S v := Finset.sum_le_sum fun u hu => hmax u hu
    _ = S.card * degIn F S v := by rw [Finset.sum_const, smul_eq_mul]

private lemma exists_greedy_order {n : ℕ} (F : Fin n → Fin n → Bool) :
    ∀ k : ℕ, ∀ S : Finset (Fin n), S.card = k →
      ∃ f : Fin k → Fin n,
        (∀ i j, f i = f j → i = j) ∧
        (∀ i, f i ∈ S) ∧
        (∀ h : ℕ, 1 < h → h ≤ k →
          let Hh : Finset (Fin n) := (Finset.univ.filter (fun i : Fin k => i.val < h)).image f
          let Hhm : Finset (Fin n) := (Finset.univ.filter (fun i : Fin k => i.val < h - 1)).image f
          h * dirEdges F Hhm ≤ (h - 2) * dirEdges F Hh) := by
  intro k
  induction k with
  | zero =>
    intro S _
    exact ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun h h1 h2 => by omega⟩
  | succ k ih =>
    intro S hScard
    have hne : S.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨v, hv, hdeg_le⟩ := exists_max_deg F S hne
    have her_card : (S.erase v).card = k := by
      rw [Finset.card_erase_of_mem hv, hScard]; omega
    obtain ⟨f', hf'_inj, hf'_mem, hf'_step⟩ := ih (S.erase v) her_card
    let f : Fin (k + 1) → Fin n := fun i =>
      if hi : i.val < k then f' ⟨i.val, hi⟩ else v
    have hf_inj : ∀ i j, f i = f j → i = j := by
      intro i j hEq
      dsimp only [f] at hEq
      by_cases hi : i.val < k <;> by_cases hj : j.val < k
      · rw [dif_pos hi, dif_pos hj] at hEq
        have := hf'_inj ⟨i.val, hi⟩ ⟨j.val, hj⟩ hEq
        exact Fin.ext (congrArg (Fin.val : Fin k → ℕ) this)
      · rw [dif_pos hi, dif_neg hj] at hEq
        have hm := hf'_mem ⟨i.val, hi⟩
        rw [hEq] at hm
        exact absurd (Finset.mem_erase.mp hm).1 (fun h => h rfl)
      · rw [dif_neg hi, dif_pos hj] at hEq
        have hm := hf'_mem ⟨j.val, hj⟩
        rw [← hEq] at hm
        exact absurd (Finset.mem_erase.mp hm).1 (fun h => h rfl)
      · exact Fin.ext (by have := i.isLt; have := j.isLt; omega)
    have hf_mem : ∀ i, f i ∈ S := by
      intro i
      dsimp only [f]
      by_cases hi : i.val < k
      · rw [dif_pos hi]
        exact Finset.erase_subset v S (hf'_mem ⟨i.val, hi⟩)
      · rw [dif_neg hi]
        exact hv
    refine ⟨f, hf_inj, hf_mem, ?_⟩
    intro h h1 hle
    have himg_eq : ∀ t : ℕ, t ≤ k →
        (Finset.univ.filter (fun i : Fin (k + 1) => i.val < t)).image f =
          (Finset.univ.filter (fun i : Fin k => i.val < t)).image f' := by
      intro t ht
      ext x
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨i, hi, rfl⟩
        have hik : i.val < k := by omega
        refine ⟨⟨i.val, hik⟩, hi, ?_⟩
        dsimp only [f]
        rw [dif_pos hik]
      · rintro ⟨i, hi, rfl⟩
        refine ⟨⟨i.val, by omega⟩, hi, ?_⟩
        dsimp only [f]
        rw [dif_pos i.isLt]
    by_cases htop : h = k + 1
    · subst htop
      have hHfull : (Finset.univ.filter (fun i : Fin (k + 1) => i.val < k + 1)).image f = S := by
        apply Finset.eq_of_subset_of_card_le
        · intro x hx
          rcases Finset.mem_image.mp hx with ⟨i, _, rfl⟩
          exact hf_mem i
        · have huniv : Finset.univ.filter (fun i : Fin (k + 1) => i.val < k + 1) = Finset.univ := by
            ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]; exact i.isLt
          rw [huniv, Finset.card_image_of_injective _ hf_inj, Finset.card_univ, Fintype.card_fin, hScard]
      have hHprev : (Finset.univ.filter (fun i : Fin (k + 1) => i.val < k + 1 - 1)).image f = S.erase v := by
        have hsub : k + 1 - 1 = k := by omega
        rw [hsub, himg_eq k le_rfl]
        apply Finset.eq_of_subset_of_card_le
        · intro x hx
          rcases Finset.mem_image.mp hx with ⟨i, _, rfl⟩
          exact hf'_mem i
        · have huniv : Finset.univ.filter (fun i : Fin k => i.val < k) = Finset.univ := by
            ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]; exact i.isLt
          rw [huniv, Finset.card_image_of_injective _ hf'_inj, Finset.card_univ, Fintype.card_fin, her_card]
      dsimp only
      rw [hHfull, hHprev]
      have her := dirEdges_erase F S v hv
      rw [hScard] at hdeg_le
      have hmul : (k + 1) * dirEdges F (S.erase v) + 2 * ((k + 1) * degIn F S v) =
          (k + 1) * dirEdges F S := by
        calc
          (k + 1) * dirEdges F (S.erase v) + 2 * ((k + 1) * degIn F S v)
              = (k + 1) * (dirEdges F (S.erase v) + 2 * degIn F S v) := by ring
          _ = (k + 1) * dirEdges F S := by rw [her]
      have h2 : 2 * dirEdges F S ≤ 2 * ((k + 1) * degIn F S v) := Nat.mul_le_mul_left 2 hdeg_le
      have hsub2 : (k + 1 - 2) * dirEdges F S + 2 * dirEdges F S = (k + 1) * dirEdges F S := by
        have : k + 1 - 2 + 2 = k + 1 := by omega
        calc
          (k + 1 - 2) * dirEdges F S + 2 * dirEdges F S = (k + 1 - 2 + 2) * dirEdges F S := by ring
          _ = (k + 1) * dirEdges F S := by rw [this]
      omega
    · have hlek : h ≤ k := by omega
      dsimp only
      rw [himg_eq h hlek, himg_eq (h - 1) (by omega)]
      exact hf'_step h h1 hlek

private lemma two_mul_ordered_eq_dirEdges {n : ℕ} (F : Fin n → Fin n → Bool)
    (order : Equiv.Perm (Fin n)) (S : Finset (Fin n)) :
    2 * ((S ×ˢ S).filter (fun z => (order z.1).val < (order z.2).val ∧ F z.1 z.2 ≠ F z.2 z.1)).card =
      dirEdges F S := by
  let A := (S ×ˢ S).filter (fun z => (order z.1).val < (order z.2).val ∧ F z.1 z.2 ≠ F z.2 z.1)
  let B := (S ×ˢ S).filter (fun z => (order z.2).val < (order z.1).val ∧ F z.1 z.2 ≠ F z.2 z.1)
  have hBcard : B.card = A.card := by
    have hB_eq : B = A.image Prod.swap := by
      ext z
      simp only [A, B, Finset.mem_image, Finset.mem_filter, Finset.mem_product, Prod.exists, Prod.swap_prod_mk]
      constructor
      · rintro ⟨⟨hz1, hz2⟩, hlt, hd⟩
        exact ⟨z.2, z.1, ⟨⟨hz2, hz1⟩, hlt, hd.symm⟩, Prod.ext rfl rfl⟩
      · rintro ⟨a, b, ⟨⟨ha, hb⟩, hlt, hd⟩, hEq⟩
        cases hEq
        exact ⟨⟨hb, ha⟩, hlt, hd.symm⟩
    rw [hB_eq, Finset.card_image_of_injective _ Prod.swap_injective]
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro z hA hB
    have a1 := (Finset.mem_filter.mp hA).2.1
    have b1 := (Finset.mem_filter.mp hB).2.1
    omega
  have hunion : A ∪ B = (S ×ˢ S).filter (fun z => F z.1 z.2 ≠ F z.2 z.1) := by
    ext z
    simp only [A, B, Finset.mem_union, Finset.mem_filter, Finset.mem_product]
    constructor
    · rintro (⟨h1, _, h2⟩ | ⟨h1, _, h2⟩) <;> exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      have hne : z.1 ≠ z.2 := fun h => h2 (by rw [h])
      have hvne : (order z.1).val ≠ (order z.2).val := fun h => hne (order.injective (Fin.ext h))
      rcases lt_or_gt_of_ne hvne with hlt | hgt
      · left; exact ⟨h1, hlt, h2⟩
      · right; exact ⟨h1, hgt, h2⟩
  unfold dirEdges
  rw [← hunion, Finset.card_union_of_disjoint hdisj, hBcard]
  ring

private lemma telescope_step (n : ℕ) (c : ℕ → ℕ)
    (hstep : ∀ h : ℕ, 1 < h → h ≤ n → h * c (h - 1) ≤ (h - 2) * c h)
    (h0 : c 0 = 0) (h1 : c 1 = 0) :
    ∀ h : ℕ, h ≤ n → n * (n - 1) * c h ≤ h * (h - 1) * c n := by
  intro h hle
  by_cases hlt2 : h < 2
  · interval_cases h
    · simp [h0]
    · simp [h1]
  · have hge2 : 2 ≤ h := by omega
    have haux : ∀ k : ℕ, h ≤ k → k ≤ n → k * (k - 1) * c h ≤ h * (h - 1) * c k := by
      intro k
      induction k with
      | zero => intro hk; omega
      | succ k ih =>
        intro hk hkn
        by_cases hEq : h = k + 1
        · subst hEq; exact le_rfl
        · have hhk : h ≤ k := by omega
          have hih := ih hhk (by omega)
          have hst := hstep (k + 1) (by omega) hkn
          have hsub1 : k + 1 - 1 = k := by omega
          have hsub2 : k + 1 - 2 = k - 1 := by omega
          rw [hsub1, hsub2] at hst
          have h1' : (k + 1) * k * (k - 1) * c h ≤ (k + 1) * (h * (h - 1) * c k) := by
            have := Nat.mul_le_mul_left (k + 1) hih
            linarith
          have h2' : (k + 1) * (h * (h - 1) * c k) ≤ h * (h - 1) * ((k - 1) * c (k + 1)) := by
            have := Nat.mul_le_mul_left (h * (h - 1)) hst
            linarith
          have h3' : (k - 1) * ((k + 1) * k * c h) ≤ (k - 1) * (h * (h - 1) * c (k + 1)) := by
            linarith
          have hkpos : 0 < k - 1 := by omega
          exact Nat.le_of_mul_le_mul_left h3' hkpos
    exact haux n hle le_rfl

end PEqualNP.Outside.L_lib_651_aux

theorem PEqualNP.Outside.L_lib_651 : (∀ (n : ℕ) (F : Fin n → Fin n → Bool),
  ∃ order : Equiv.Perm (Fin n),
    let exposed := fun h : ℕ => Finset.univ.filter (fun i : Fin n => h ≤ (order i).val)
    let cost := fun (h : ℕ) (out : Finset (Fin n) → Finset (Fin n) → Bool) =>
      (Finset.univ.filter (fun z : Fin n × Fin n =>
        out ({z.1,z.2} : Finset (Fin n)) (exposed h ∩ {z.1}) ≠ F z.1 z.2)).card
    ∃ D : Finset (Fin n) → Finset (Fin n) → Bool,
      (∀ h : ℕ, h ≤ n → ∀ other, cost h D ≤ cost h other) ∧
      (∀ h : ℕ, 1 < h → h ≤ n → h * cost (h-1) D ≤ (h-2) * cost h D) ∧
      (∀ h : ℕ, h ≤ n → n*(n-1)*cost h D ≤ h*(h-1)*cost n D)) := by
  classical
  intro n F
  have huniv_card : (Finset.univ : Finset (Fin n)).card = n := by simp
  obtain ⟨f, hf_inj, _, hf_step⟩ :=
    PEqualNP.Outside.L_lib_651_aux.exists_greedy_order F n Finset.univ huniv_card
  have hf_bij : Function.Bijective f := (Finite.injective_iff_bijective).mp hf_inj
  let e : Fin n ≃ Fin n := Equiv.ofBijective f hf_bij
  let order : Equiv.Perm (Fin n) := e.symm
  refine ⟨order, ?_⟩
  intro exposed cost
  let otherIn : Finset (Fin n) → Fin n → Fin n := fun pair i =>
    if h : (pair.erase i).Nonempty then Classical.choose h else i
  have hother_pair : ∀ a b : Fin n, otherIn ({a, b} : Finset (Fin n)) a = b := by
    intro a b
    dsimp only [otherIn]
    by_cases hab : a = b
    · subst hab
      have hemp : ¬ (({a, a} : Finset (Fin n)).erase a).Nonempty := by
        simp
      rw [dif_neg hemp]
    · have hne : (({a, b} : Finset (Fin n)).erase a).Nonempty := by
        refine ⟨b, Finset.mem_erase.mpr ⟨Ne.symm hab, by simp⟩⟩
      rw [dif_pos hne]
      have hmem := Classical.choose_spec hne
      rcases Finset.mem_erase.mp hmem with ⟨hne_a, hpair⟩
      rcases Finset.mem_insert.mp hpair with hEq | hsing
      · exact absurd hEq hne_a
      · exact Finset.mem_singleton.mp hsing
  let minOrd : Finset (Fin n) → Option (Fin n) := fun pair =>
    if h : pair.Nonempty then
      some (Classical.choose (Finset.exists_min_image pair (fun i => (order i).val) h))
    else none
  have hminOrd_pair : ∀ a b : Fin n,
      minOrd ({a, b} : Finset (Fin n)) = some (if (order a).val ≤ (order b).val then a else b) := by
    intro a b
    dsimp only [minOrd]
    have hne : ({a, b} : Finset (Fin n)).Nonempty := ⟨a, by simp⟩
    rw [dif_pos hne]
    congr 1
    set m := Classical.choose (Finset.exists_min_image ({a, b} : Finset (Fin n)) (fun i => (order i).val) hne)
    have hm_spec := Classical.choose_spec (Finset.exists_min_image ({a, b} : Finset (Fin n)) (fun i => (order i).val) hne)
    have hm_mem : m = a ∨ m = b := by
      rcases Finset.mem_insert.mp hm_spec.1 with h1 | h2
      · left; exact h1
      · right; exact Finset.mem_singleton.mp h2
    have hle_a : (order m).val ≤ (order a).val := hm_spec.2 a (by simp)
    have hle_b : (order m).val ≤ (order b).val := hm_spec.2 b (by simp)
    by_cases hab : (order a).val ≤ (order b).val
    · rw [if_pos hab]
      rcases hm_mem with hma | hmb
      · exact hma
      · rw [hmb] at hle_a ⊢
        have hEq : (order b).val = (order a).val := le_antisymm hle_a hab
        exact order.injective (Fin.ext hEq)
    · rw [if_neg hab]
      rcases hm_mem with hma | hmb
      · rw [hma] at hle_b
        exfalso; omega
      · exact hmb
  let D : Finset (Fin n) → Finset (Fin n) → Bool := fun pair rep =>
    if hr : rep.Nonempty then
      let i := Classical.choose hr
      F i (otherIn pair i)
    else
      match minOrd pair with
      | some i => F i (otherIn pair i)
      | none => false
  have hD_eval : ∀ h : ℕ, ∀ z : Fin n × Fin n,
      (D ({z.1, z.2} : Finset (Fin n)) (exposed h ∩ {z.1}) ≠ F z.1 z.2) ↔
      ((order z.2).val < (order z.1).val ∧ (order z.1).val < h ∧ F z.1 z.2 ≠ F z.2 z.1) := by
    intro h z
    by_cases hexp : h ≤ (order z.1).val
    · have hrep : exposed h ∩ {z.1} = {z.1} := by
        ext x
        simp only [exposed, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_singleton]
        constructor
        · exact fun hx => hx.2
        · rintro rfl; exact ⟨hexp, rfl⟩
      have hne : (exposed h ∩ {z.1}).Nonempty := by rw [hrep]; exact ⟨z.1, by simp⟩
      have hch : Classical.choose hne = z.1 :=
        Finset.mem_singleton.mp (Finset.mem_inter.mp (Classical.choose_spec hne)).2
      have hval : D ({z.1, z.2} : Finset (Fin n)) (exposed h ∩ {z.1}) = F z.1 z.2 := by
        dsimp only [D]
        rw [dif_pos hne, hch, hother_pair]
      rw [hval]
      constructor
      · intro hc; exact absurd rfl hc
      · rintro ⟨_, hlt, _⟩; omega
    · have hlt1 : (order z.1).val < h := by omega
      have hrep : exposed h ∩ {z.1} = ∅ := by
        ext x
        simp only [exposed, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_singleton, Finset.notMem_empty, iff_false]
        rintro ⟨hx1, rfl⟩
        omega
      have hnotne : ¬ (exposed h ∩ {z.1}).Nonempty := by rw [hrep]; simp
      have hDval : D ({z.1, z.2} : Finset (Fin n)) (exposed h ∩ {z.1}) =
          if (order z.1).val ≤ (order z.2).val then F z.1 z.2 else F z.2 z.1 := by
        dsimp only [D]
        rw [dif_neg hnotne, hminOrd_pair z.1 z.2]
        dsimp only
        by_cases hle : (order z.1).val ≤ (order z.2).val
        · rw [if_pos hle, if_pos hle]
          exact congrArg (F z.1) (hother_pair z.1 z.2)
        · rw [if_neg hle, if_neg hle]
          have hpair_comm : ({z.1, z.2} : Finset (Fin n)) = {z.2, z.1} := by
            ext x; simp [or_comm]
          rw [hpair_comm, hother_pair z.2 z.1]
      rw [hDval]
      by_cases hle : (order z.1).val ≤ (order z.2).val
      · rw [if_pos hle]
        constructor
        · intro hc; exact absurd rfl hc
        · rintro ⟨hgt, _, _⟩; omega
      · rw [if_neg hle]
        have hgt : (order z.2).val < (order z.1).val := by omega
        constructor
        · intro hd; exact ⟨hgt, hlt1, hd.symm⟩
        · rintro ⟨_, _, hd⟩; exact hd.symm
  have hcost_two : ∀ h : ℕ, h ≤ n →
      let Hh : Finset (Fin n) := (Finset.univ.filter (fun i : Fin n => i.val < h)).image f
      2 * cost h D = PEqualNP.Outside.L_lib_651_aux.dirEdges F Hh := by
    intro h _ Hh
    have hHh_mem : ∀ x : Fin n, x ∈ Hh ↔ (order x).val < h := by
      intro x
      dsimp only [Hh]
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨i, hi, rfl⟩
        have hinv : order (f i) = i := e.symm_apply_apply i
        rw [hinv]; exact hi
      · intro hx
        refine ⟨order x, hx, ?_⟩
        exact e.apply_symm_apply x
    have herr_eq :
        Finset.univ.filter (fun z : Fin n × Fin n =>
          D ({z.1, z.2} : Finset (Fin n)) (exposed h ∩ {z.1}) ≠ F z.1 z.2) =
        ((Hh ×ˢ Hh).filter (fun z => (order z.1).val < (order z.2).val ∧ F z.1 z.2 ≠ F z.2 z.1)).image
          Prod.swap := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_product,
        Prod.exists, Prod.swap_prod_mk]
      rw [hD_eval h z]
      constructor
      · rintro ⟨hlt, h1h, hd⟩
        refine ⟨z.2, z.1, ⟨⟨(hHh_mem z.2).mpr (by omega), (hHh_mem z.1).mpr h1h⟩, hlt, hd.symm⟩,
          Prod.ext rfl rfl⟩
      · rintro ⟨a, b, ⟨⟨_, hb⟩, hlt, hd⟩, hEq⟩
        cases hEq
        exact ⟨hlt, (hHh_mem b).mp hb, hd.symm⟩
    dsimp only [cost]
    rw [herr_eq, Finset.card_image_of_injective _ Prod.swap_injective]
    exact PEqualNP.Outside.L_lib_651_aux.two_mul_ordered_eq_dirEdges F order Hh
  have hstep_cost : ∀ h : ℕ, 1 < h → h ≤ n → h * cost (h - 1) D ≤ (h - 2) * cost h D := by
    intro h h1 hle
    have hst := hf_step h h1 hle
    have hc1 := hcost_two h hle
    have hc0 := hcost_two (h - 1) (by omega)
    dsimp only at hst hc1 hc0
    rw [← hc1, ← hc0] at hst
    exact Nat.le_of_mul_le_mul_left (by linarith) (by decide : 0 < 2)
  refine ⟨D, ?_, hstep_cost, ?_⟩
  · intro h _ other
    let errD := Finset.univ.filter (fun z : Fin n × Fin n =>
      D ({z.1, z.2} : Finset (Fin n)) (exposed h ∩ {z.1}) ≠ F z.1 z.2)
    let errO := Finset.univ.filter (fun z : Fin n × Fin n =>
      other ({z.1, z.2} : Finset (Fin n)) (exposed h ∩ {z.1}) ≠ F z.1 z.2)
    let φ : Fin n × Fin n → Fin n × Fin n := fun z =>
      if other ({z.1, z.2} : Finset (Fin n)) (exposed h ∩ {z.1}) ≠ F z.1 z.2 then z else z.swap
    have hmaps : ∀ z ∈ errD, φ z ∈ errO := by
      intro z hz
      have hDz := (hD_eval h z).mp (Finset.mem_filter.mp hz).2
      dsimp only [φ]
      by_cases ho : other ({z.1, z.2} : Finset (Fin n)) (exposed h ∩ {z.1}) ≠ F z.1 z.2
      · rw [if_pos ho]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ z, ho⟩
      · rw [if_neg ho]
        push_neg at ho
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ z.swap, ?_⟩
        have hpair : ({z.2, z.1} : Finset (Fin n)) = {z.1, z.2} := by ext x; simp [or_comm]
        have hrep1 : exposed h ∩ {z.1} = ∅ := by
          ext x; simp only [exposed, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.mem_singleton, Finset.notMem_empty, iff_false]
          rintro ⟨hx, rfl⟩; omega
        have hrep2 : exposed h ∩ {z.2} = ∅ := by
          ext x; simp only [exposed, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.mem_singleton, Finset.notMem_empty, iff_false]
          rintro ⟨hx, rfl⟩; omega
        dsimp only [Prod.swap]
        rw [hpair, hrep2, ← hrep1, ho]
        exact hDz.2.2
    have hinj : Set.InjOn φ (↑errD : Set (Fin n × Fin n)) := by
      intro z1 hz1 z2 hz2 hEq
      have h1 := (hD_eval h z1).mp (Finset.mem_filter.mp hz1).2
      have h2 := (hD_eval h z2).mp (Finset.mem_filter.mp hz2).2
      dsimp only [φ] at hEq
      split_ifs at hEq with c1 c2 c2
      · exact hEq
      · exfalso
        have h1a := congrArg Prod.fst hEq
        have h1b := congrArg Prod.snd hEq
        dsimp only [Prod.swap] at h1a h1b
        rw [h1a, h1b] at h1
        omega
      · exfalso
        have h1a := congrArg Prod.fst hEq
        have h1b := congrArg Prod.snd hEq
        dsimp only [Prod.swap] at h1a h1b
        rw [← h1a, ← h1b] at h2
        omega
      · exact Prod.swap_injective hEq
    exact Finset.card_le_card_of_injOn φ hmaps hinj
  · have hc0 : cost 0 D = 0 := by
      dsimp only [cost]
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro z _
      rw [hD_eval 0 z]
      rintro ⟨_, hlt, _⟩
      omega
    have hc1 : cost 1 D = 0 := by
      dsimp only [cost]
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro z _
      rw [hD_eval 1 z]
      rintro ⟨hgt, hlt, _⟩
      omega
    exact PEqualNP.Outside.L_lib_651_aux.telescope_step n (fun h => cost h D) hstep_cost hc0 hc1
