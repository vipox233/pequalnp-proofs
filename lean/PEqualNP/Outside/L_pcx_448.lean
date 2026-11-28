import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_448_aux

open scoped BigOperators

lemma zmod2_add_self (x : ZMod 2) : x + x = 0 := by
  fin_cases x <;> decide

lemma zmod2_mul_self (x : ZMod 2) : x * x = x := by
  fin_cases x
  · rfl
  · rfl

lemma zmod2_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma zmod2_pow_eq_self (u : ZMod 2) (k : ℕ) (hk : 1 ≤ k) : u ^ k = u := by
  rcases zmod2_eq_zero_or_one u with rfl | rfl
  · exact zero_pow (by omega)
  · exact one_pow k

noncomputable def splitA {n : ℕ} (p : MvPolynomial (Fin n ⊕ Unit) (ZMod 2)) :
    MvPolynomial (Fin n) (ZMod 2) :=
  ∑ s ∈ p.support.filter (fun s => s (Sum.inr ()) = 0),
    MvPolynomial.monomial (s.comapDomain Sum.inl Sum.inl_injective.injOn) (p.coeff s)

noncomputable def splitB {n : ℕ} (p : MvPolynomial (Fin n ⊕ Unit) (ZMod 2)) :
    MvPolynomial (Fin n) (ZMod 2) :=
  ∑ s ∈ p.support.filter (fun s => 1 ≤ s (Sum.inr ())),
    MvPolynomial.monomial (s.comapDomain Sum.inl Sum.inl_injective.injOn) (p.coeff s)

lemma comap_sum_add_inr {n : ℕ} (s : (Fin n ⊕ Unit) →₀ ℕ) :
    (s.comapDomain Sum.inl Sum.inl_injective.injOn).sum (fun _ k => k) + s (Sum.inr ()) =
      s.sum (fun _ k => k) := by
  have hL : (s.comapDomain Sum.inl Sum.inl_injective.injOn).sum (fun _ k => k) =
      ∑ i : Fin n, s (Sum.inl i) := by
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
    refine Finset.sum_congr rfl (fun i _ => rfl)
  have hR : s.sum (fun _ k => k) = (∑ i : Fin n, s (Sum.inl i)) + s (Sum.inr ()) := by
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fintype.sum_sum_type, Fintype.sum_unique (ι := Unit)]
  rw [hL, hR]

lemma eval_monomial_split {n : ℕ} (s : (Fin n ⊕ Unit) →₀ ℕ) (c : ZMod 2)
    (x : Fin n → ZMod 2) (u : ZMod 2) :
    MvPolynomial.eval (Sum.elim x (fun _ => u)) (MvPolynomial.monomial s c) =
      MvPolynomial.eval x (MvPolynomial.monomial (s.comapDomain Sum.inl Sum.inl_injective.injOn) c) *
        u ^ (s (Sum.inr ())) := by
  rw [MvPolynomial.eval_monomial, MvPolynomial.eval_monomial, mul_assoc]
  congr 1
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    Fintype.prod_sum_type, Fintype.prod_unique (ι := Unit)]
  rfl

lemma eval_eq_split {n : ℕ} (p : MvPolynomial (Fin n ⊕ Unit) (ZMod 2))
    (x : Fin n → ZMod 2) (u : ZMod 2) :
    MvPolynomial.eval (Sum.elim x (fun _ => u)) p =
      MvPolynomial.eval x (splitA p) + u * MvPolynomial.eval x (splitB p) := by
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  have hpart : (∑ s ∈ p.support, MvPolynomial.eval (Sum.elim x (fun _ => u)) (MvPolynomial.monomial s (p.coeff s))) =
      (∑ s ∈ p.support.filter (fun s => s (Sum.inr ()) = 0),
        MvPolynomial.eval (Sum.elim x (fun _ => u)) (MvPolynomial.monomial s (p.coeff s))) +
      (∑ s ∈ p.support.filter (fun s => ¬ (s (Sum.inr ()) = 0)),
        MvPolynomial.eval (Sum.elim x (fun _ => u)) (MvPolynomial.monomial s (p.coeff s))) :=
    (Finset.sum_filter_add_sum_filter_not p.support (fun s => s (Sum.inr ()) = 0) _).symm
  rw [hpart]
  have hfilt : p.support.filter (fun s => ¬ (s (Sum.inr ()) = 0)) =
      p.support.filter (fun s => 1 ≤ s (Sum.inr ())) := by
    ext s
    simp only [Finset.mem_filter]
    exact ⟨fun ⟨h1, h2⟩ => ⟨h1, by omega⟩, fun ⟨h1, h2⟩ => ⟨h1, by omega⟩⟩
  rw [hfilt, splitA, splitB, map_sum, map_sum, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl (fun s hs => ?_)
    have h0 : s (Sum.inr ()) = 0 := (Finset.mem_filter.mp hs).2
    rw [eval_monomial_split, h0, pow_zero, mul_one]
  · refine Finset.sum_congr rfl (fun s hs => ?_)
    have h1 : 1 ≤ s (Sum.inr ()) := (Finset.mem_filter.mp hs).2
    rw [eval_monomial_split, zmod2_pow_eq_self u _ h1, mul_comm]

lemma totalDegree_finset_sum_le {σ ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → MvPolynomial σ (ZMod 2)) (D : ℕ) (h : ∀ i ∈ s, (f i).totalDegree ≤ D) :
    (∑ i ∈ s, f i).totalDegree ≤ D := by
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, MvPolynomial.totalDegree_zero]
    exact Nat.zero_le D
  | insert a t hat ih =>
    rw [Finset.sum_insert hat]
    refine le_trans (MvPolynomial.totalDegree_add _ _) (max_le ?_ ?_)
    · exact h a (Finset.mem_insert_self a t)
    · exact ih (fun i hi => h i (Finset.mem_insert_of_mem hi))

lemma totalDegree_splitA_le {n : ℕ} (p : MvPolynomial (Fin n ⊕ Unit) (ZMod 2)) :
    (splitA p).totalDegree ≤ p.totalDegree := by
  rw [splitA]
  refine totalDegree_finset_sum_le _ _ p.totalDegree (fun s hs => ?_)
  have hs_mem : s ∈ p.support := (Finset.mem_filter.mp hs).1
  refine le_trans (MvPolynomial.totalDegree_monomial_le _ _) ?_
  have hle : s.sum (fun _ k => k) ≤ p.totalDegree := Finset.le_sup (f := fun t => t.sum (fun _ k => k)) hs_mem
  have hsum := comap_sum_add_inr s
  change (s.comapDomain Sum.inl Sum.inl_injective.injOn).sum (fun _ k => k) ≤ p.totalDegree
  omega

lemma totalDegree_splitB_le {n d : ℕ} (p : MvPolynomial (Fin n ⊕ Unit) (ZMod 2))
    (hp : p.totalDegree ≤ d + 1) :
    (splitB p).totalDegree ≤ d := by
  rw [splitB]
  refine totalDegree_finset_sum_le _ _ d (fun s hs => ?_)
  have hs_mem : s ∈ p.support := (Finset.mem_filter.mp hs).1
  have hs_pos : 1 ≤ s (Sum.inr ()) := (Finset.mem_filter.mp hs).2
  refine le_trans (MvPolynomial.totalDegree_monomial_le _ _) ?_
  have hle : s.sum (fun _ k => k) ≤ p.totalDegree := Finset.le_sup (f := fun t => t.sum (fun _ k => k)) hs_mem
  have hsum := comap_sum_add_inr s
  change (s.comapDomain Sum.inl Sum.inl_injective.injOn).sum (fun _ k => k) ≤ d
  omega

lemma sum_eval_monomial_eq_zero {N : ℕ} (m : Fin N →₀ ℕ) (c : ZMod 2)
    (hm : m.sum (fun _ k => k) < N) :
    (∑ x : Fin N → ZMod 2, MvPolynomial.eval x (MvPolynomial.monomial m c)) = 0 := by
  have hex : ∃ i0 : Fin N, m i0 = 0 := by
    by_contra hall
    push_neg at hall
    have hge : N ≤ m.sum (fun _ k => k) := by
      rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
      calc
        N = ∑ _i : Fin N, 1 := by simp
        _ ≤ ∑ i : Fin N, m i := Finset.sum_le_sum (fun i _ => Nat.pos_of_ne_zero (hall i))
    omega
  rcases hex with ⟨i0, hi0⟩
  let flip : (Fin N → ZMod 2) → (Fin N → ZMod 2) := fun x => Function.update x i0 (x i0 + 1)
  have hflip_inv : ∀ x, flip (flip x) = x := by
    intro x
    ext i
    by_cases h : i = i0
    · subst h; simp [flip, add_assoc, zmod2_add_self]
    · simp [flip, h]
  have hflip_eval : ∀ x, MvPolynomial.eval (flip x) (MvPolynomial.monomial m c) =
      MvPolynomial.eval x (MvPolynomial.monomial m c) := by
    intro x
    rw [MvPolynomial.eval_monomial, MvPolynomial.eval_monomial]
    congr 1
    rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    by_cases h : i = i0
    · subst h; simp [hi0]
    · simp [flip, h]
  let S0 : Finset (Fin N → ZMod 2) := Finset.univ.filter (fun x => x i0 = 0)
  let S1 : Finset (Fin N → ZMod 2) := Finset.univ.filter (fun x => x i0 ≠ 0)
  have hS1_eq : S1 = S0.image flip := by
    ext x
    simp only [S1, S0, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hx
      refine ⟨flip x, ?_, hflip_inv x⟩
      rcases zmod2_eq_zero_or_one (x i0) with h0 | h1
      · exact (hx h0).elim
      · simp [flip, h1, zmod2_add_self]
    · rintro ⟨y, hy, rfl⟩
      simp [flip, hy]
  have hsplit := (Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin N → ZMod 2))
    (fun x => x i0 = 0) (fun x => MvPolynomial.eval x (MvPolynomial.monomial m c))).symm
  rw [hsplit]
  change (∑ x ∈ S0, MvPolynomial.eval x (MvPolynomial.monomial m c)) +
    (∑ x ∈ S1, MvPolynomial.eval x (MvPolynomial.monomial m c)) = 0
  rw [hS1_eq, Finset.sum_image (fun x₁ _ x₂ _ h => by have := congrArg flip h; rwa [hflip_inv, hflip_inv] at this)]
  have heq_sum : (∑ x ∈ S0, MvPolynomial.eval (flip x) (MvPolynomial.monomial m c)) =
      ∑ x ∈ S0, MvPolynomial.eval x (MvPolynomial.monomial m c) :=
    Finset.sum_congr rfl (fun x _ => hflip_eval x)
  rw [heq_sum, zmod2_add_self]

lemma sum_eval_eq_zero_of_lt {N : ℕ} (p : MvPolynomial (Fin N) (ZMod 2))
    (hp : p.totalDegree < N) :
    (∑ x : Fin N → ZMod 2, MvPolynomial.eval x p) = 0 := by
  conv_lhs =>
    arg 2
    ext x
    rw [p.as_sum, map_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero (fun m hm => ?_)
  have hmlt : m.sum (fun _ k => k) < N :=
    lt_of_le_of_lt (Finset.le_sup (f := fun t => t.sum (fun _ k => k)) hm) hp
  exact sum_eval_monomial_eq_zero m (p.coeff m) hmlt

lemma card_strict_pairs (m : ℕ) :
    ((Finset.univ : Finset (Fin m × Fin m)).filter (fun p => p.1 < p.2)).card = m.choose 2 := by
  let e : (Fin m × Fin m) → Finset (Fin m) := fun p => {p.1, p.2}
  let S : Finset (Fin m × Fin m) := Finset.univ.filter (fun p => p.1 < p.2)
  have he_inj : Set.InjOn e (S : Set (Fin m × Fin m)) := by
    intro p₁ hp₁ p₂ hp₂ h
    change ({p₁.1, p₁.2} : Finset (Fin m)) = {p₂.1, p₂.2} at h
    have hlt1 : p₁.1 < p₁.2 := (Finset.mem_filter.mp hp₁).2
    have hlt2 : p₂.1 < p₂.2 := (Finset.mem_filter.mp hp₂).2
    have h1mem : p₁.1 ∈ ({p₂.1, p₂.2} : Finset (Fin m)) := h ▸ Finset.mem_insert_self p₁.1 {p₁.2}
    have h2mem : p₁.2 ∈ ({p₂.1, p₂.2} : Finset (Fin m)) := h ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self p₁.2)
    have h3mem : p₂.1 ∈ ({p₁.1, p₁.2} : Finset (Fin m)) := h.symm ▸ Finset.mem_insert_self p₂.1 {p₂.2}
    have h4mem : p₂.2 ∈ ({p₁.1, p₁.2} : Finset (Fin m)) := h.symm ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self p₂.2)
    simp only [Finset.mem_insert, Finset.mem_singleton] at h1mem h2mem h3mem h4mem
    apply Prod.ext <;> apply Fin.ext <;>
    rcases h1mem with h1 | h1 <;> rcases h2mem with h2 | h2 <;>
    rcases h3mem with h3 | h3 <;> rcases h4mem with h4 | h4 <;>
    simp only [Fin.lt_iff_val_lt_val, Fin.ext_iff] at hlt1 hlt2 h1 h2 h3 h4 <;> omega
  have himg : S.image e = (Finset.univ : Finset (Fin m)).powersetCard 2 := by
    ext T
    simp only [Finset.mem_image, S, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_powersetCard, Finset.subset_univ, e]
    constructor
    · rintro ⟨⟨a, b⟩, hab, rfl⟩
      exact Finset.card_pair (ne_of_lt hab)
    · intro hcard
      rcases Finset.card_eq_two.mp hcard with ⟨a, b, hab, rfl⟩
      rcases lt_or_gt_of_ne hab with hlt | hgt
      · exact ⟨(a, b), hlt, rfl⟩
      · exact ⟨(b, a), hgt, Finset.pair_comm b a⟩
  calc
    S.card = (S.image e).card := (Finset.card_image_of_injOn he_inj).symm
    _ = ((Finset.univ : Finset (Fin m)).powersetCard 2).card := by rw [himg]
    _ = m.choose 2 := by rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

end PEqualNP.Outside.L_pcx_448_aux

theorem PEqualNP.Outside.L_pcx_448 :
  ∀ d : ℕ,
  let K := ZMod 2
  let bound := 2*d+1
  (∀ n m : ℕ,
    let P := MvPolynomial (Fin n ⊕ Unit) K
    let S := MvPolynomial (Fin n) K
    ∀ F : Fin m → P, (∀ i, (F i).totalDegree ≤ d+1) →
      ∃ G : Finset S, G.card ≤ m + m.choose 2 ∧
        (∀ p ∈ G, p.totalDegree ≤ bound) ∧
        ∀ x : Fin n → K,
          (∃ u : K, ∀ i, MvPolynomial.eval (Sum.elim x (fun _ => u)) (F i) = 0) ↔
          ∀ p ∈ G, MvPolynomial.eval x p = 0) ∧
  ∃ f : MvPolynomial (Fin bound ⊕ Unit) K, f.totalDegree ≤ d+1 ∧
    (∀ x : Fin bound → K,
      (∃ u : K, MvPolynomial.eval (Sum.elim x (fun _ => u)) f = 0) ↔ ∃ i, x i = 0) ∧
    ∀ G : Finset (MvPolynomial (Fin bound) K),
      (∀ x : Fin bound → K,
        (∃ u : K, MvPolynomial.eval (Sum.elim x (fun _ => u)) f = 0) ↔
        ∀ p ∈ G, MvPolynomial.eval x p = 0) →
      ∃ p ∈ G, bound ≤ p.totalDegree := by
  intro d K bound
  constructor
  · intro n m P S F hdeg
    let a : Fin m → S := fun i => PEqualNP.Outside.L_pcx_448_aux.splitA (F i)
    let b : Fin m → S := fun i => PEqualNP.Outside.L_pcx_448_aux.splitB (F i)
    have ha_deg : ∀ i, (a i).totalDegree ≤ d + 1 := fun i =>
      le_trans (PEqualNP.Outside.L_pcx_448_aux.totalDegree_splitA_le (F i)) (hdeg i)
    have hb_deg : ∀ i, (b i).totalDegree ≤ d := fun i =>
      PEqualNP.Outside.L_pcx_448_aux.totalDegree_splitB_le (F i) (hdeg i)
    let G1 : Finset S := (Finset.univ : Finset (Fin m)).image (fun i => a i * (1 + b i))
    let pairs : Finset (Fin m × Fin m) := Finset.univ.filter (fun p => p.1 < p.2)
    let G2 : Finset S := pairs.image (fun p => a p.1 * b p.2 + a p.2 * b p.1)
    let G : Finset S := G1 ∪ G2
    refine ⟨G, ?_, ?_, ?_⟩
    · calc
        G.card ≤ G1.card + G2.card := Finset.card_union_le G1 G2
        _ ≤ (Finset.univ : Finset (Fin m)).card + pairs.card :=
            Nat.add_le_add Finset.card_image_le Finset.card_image_le
        _ = m + m.choose 2 := by
            rw [Finset.card_univ, Fintype.card_fin, PEqualNP.Outside.L_pcx_448_aux.card_strict_pairs]
    · intro p hp
      rcases Finset.mem_union.mp hp with hp1 | hp2
      · rcases Finset.mem_image.mp hp1 with ⟨i, _, rfl⟩
        have h1b : (1 + b i).totalDegree ≤ d := by
          refine le_trans (MvPolynomial.totalDegree_add 1 (b i)) ?_
          rw [MvPolynomial.totalDegree_one]
          exact max_le (Nat.zero_le d) (hb_deg i)
        refine le_trans (MvPolynomial.totalDegree_mul (a i) (1 + b i)) ?_
        have h1 := ha_deg i
        omega
      · rcases Finset.mem_image.mp hp2 with ⟨⟨i, j⟩, _, rfl⟩
        refine le_trans (MvPolynomial.totalDegree_add _ _) ?_
        refine max_le ?_ ?_
        · refine le_trans (MvPolynomial.totalDegree_mul (a i) (b j)) ?_
          have h1 := ha_deg i; have h2 := hb_deg j; omega
        · refine le_trans (MvPolynomial.totalDegree_mul (a j) (b i)) ?_
          have h1 := ha_deg j; have h2 := hb_deg i; omega
    · intro x
      let A : Fin m → ZMod 2 := fun i => MvPolynomial.eval x (a i)
      let B : Fin m → ZMod 2 := fun i => MvPolynomial.eval x (b i)
      have hevF : ∀ (u : ZMod 2) (i : Fin m),
          MvPolynomial.eval (Sum.elim x (fun _ => u)) (F i) = A i + u * B i :=
        fun u i => PEqualNP.Outside.L_pcx_448_aux.eval_eq_split (F i) x u
      constructor
      · rintro ⟨u, hu⟩ p hp
        have hAi : ∀ i, A i = u * B i := by
          intro i
          have h0 := hu i
          rw [hevF u i] at h0
          have h1 := congrArg (fun z => z + u * B i) h0
          rw [add_assoc, PEqualNP.Outside.L_pcx_448_aux.zmod2_add_self, add_zero, zero_add] at h1
          exact h1
        rcases Finset.mem_union.mp hp with hp1 | hp2
        · rcases Finset.mem_image.mp hp1 with ⟨i, _, rfl⟩
          simp only [map_mul, map_add, map_one]
          change A i * (1 + B i) = 0
          rw [hAi i, mul_add, mul_one, mul_assoc, PEqualNP.Outside.L_pcx_448_aux.zmod2_mul_self,
            PEqualNP.Outside.L_pcx_448_aux.zmod2_add_self]
        · rcases Finset.mem_image.mp hp2 with ⟨⟨i, j⟩, _, rfl⟩
          simp only [map_add, map_mul]
          change A i * B j + A j * B i = 0
          rw [hAi i, hAi j]
          have hcomm : u * B i * B j = u * B j * B i := by ring
          rw [hcomm, PEqualNP.Outside.L_pcx_448_aux.zmod2_add_self]
      · intro hG
        have hG1 : ∀ i : Fin m, A i * (1 + B i) = 0 := by
          intro i
          have hmem : a i * (1 + b i) ∈ G :=
            Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩))
          have h := hG (a i * (1 + b i)) hmem
          simp only [map_mul, map_add, map_one] at h
          exact h
        have hG2 : ∀ i j : Fin m, A i * B j + A j * B i = 0 := by
          intro i j
          rcases lt_trichotomy i j with hlt | rfl | hgt
          · have hmem : a i * b j + a j * b i ∈ G :=
              Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr
                ⟨(i, j), Finset.mem_filter.mpr ⟨Finset.mem_univ (i, j), hlt⟩, rfl⟩))
            have h := hG (a i * b j + a j * b i) hmem
            simp only [map_add, map_mul] at h
            exact h
          · exact PEqualNP.Outside.L_pcx_448_aux.zmod2_add_self _
          · have hmem : a j * b i + a i * b j ∈ G :=
              Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr
                ⟨(j, i), Finset.mem_filter.mpr ⟨Finset.mem_univ (j, i), hgt⟩, rfl⟩))
            have h := hG (a j * b i + a i * b j) hmem
            simp only [map_add, map_mul] at h
            rw [add_comm]
            exact h
        by_cases hB0 : ∀ i : Fin m, B i = 0
        · refine ⟨0, fun i => ?_⟩
          rw [hevF 0 i, zero_mul, add_zero]
          have h1 := hG1 i
          rw [hB0 i, add_zero, mul_one] at h1
          exact h1
        · push_neg at hB0
          rcases hB0 with ⟨j, hj⟩
          have hBj : B j = 1 := by
            rcases PEqualNP.Outside.L_pcx_448_aux.zmod2_eq_zero_or_one (B j) with h0 | h1
            · exact (hj h0).elim
            · exact h1
          refine ⟨A j, fun i => ?_⟩
          rw [hevF (A j) i]
          have h2 := hG2 i j
          rw [hBj, mul_one] at h2
          exact h2
  · let S1 : Finset (Fin bound) := Finset.univ.filter (fun i : Fin bound => i.val < d + 1)
    let S2 : Finset (Fin bound) := Finset.univ.filter (fun i : Fin bound => d + 1 ≤ i.val)
    have hS1_card : S1.card = d + 1 := by
      let emb : Fin (d + 1) → Fin bound := fun i => ⟨i.val, by omega⟩
      have hinj : Function.Injective emb := fun i₁ i₂ h => Fin.ext (congrArg (Fin.val (n := bound)) h)
      have heq : S1 = (Finset.univ : Finset (Fin (d + 1))).image emb := by
        ext j
        simp only [S1, emb, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
        exact ⟨fun hj => ⟨⟨j.val, hj⟩, rfl⟩, fun ⟨i, hi⟩ => hi ▸ i.isLt⟩
      rw [heq, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
    have hS2_card : S2.card = d := by
      have htot := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin bound)))
        (p := fun i : Fin bound => i.val < d + 1)
      have hfilt : (Finset.univ : Finset (Fin bound)).filter (fun i => ¬ i.val < d + 1) = S2 := by
        ext i; simp only [S2, Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
      rw [hfilt, Finset.card_univ, Fintype.card_fin] at htot
      change S1.card + S2.card = bound at htot
      omega
    let A : MvPolynomial (Fin bound ⊕ Unit) K := ∏ i ∈ S1, MvPolynomial.X (Sum.inl i)
    let B : MvPolynomial (Fin bound ⊕ Unit) K := ∏ i ∈ S2, MvPolynomial.X (Sum.inl i)
    let f : MvPolynomial (Fin bound ⊕ Unit) K := A + MvPolynomial.X (Sum.inr ()) * (1 + B)
    have hprod_deg : ∀ s : Finset (Fin bound),
        (∏ i ∈ s, (MvPolynomial.X (Sum.inl i) : MvPolynomial (Fin bound ⊕ Unit) K)).totalDegree ≤ s.card := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp [MvPolynomial.totalDegree_one]
      | insert a t hat ih =>
        rw [Finset.prod_insert hat, Finset.card_insert_of_notMem hat]
        refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
        rw [MvPolynomial.totalDegree_X]
        omega
    have hA_deg : A.totalDegree ≤ d + 1 := hS1_card ▸ hprod_deg S1
    have hB_deg : B.totalDegree ≤ d := hS2_card ▸ hprod_deg S2
    have hf_deg : f.totalDegree ≤ d + 1 := by
      refine le_trans (MvPolynomial.totalDegree_add _ _) (max_le hA_deg ?_)
      refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
      rw [MvPolynomial.totalDegree_X]
      have h1B : (1 + B).totalDegree ≤ d := by
        refine le_trans (MvPolynomial.totalDegree_add 1 B) ?_
        rw [MvPolynomial.totalDegree_one]
        exact max_le (Nat.zero_le d) hB_deg
      omega
    have hf_eval : ∀ x : Fin bound → K,
        (∃ u : K, MvPolynomial.eval (Sum.elim x (fun _ => u)) f = 0) ↔ ∃ i, x i = 0 := by
      intro x
      have hev : ∀ u : K, MvPolynomial.eval (Sum.elim x (fun _ => u)) f =
          (∏ i ∈ S1, x i) + u * (1 + ∏ i ∈ S2, x i) := by
        intro u
        simp [f, A, B, map_add, map_mul, map_prod]
      constructor
      · rintro ⟨u, hu⟩
        rw [hev u] at hu
        by_contra hall
        push_neg at hall
        have hx1 : ∀ i : Fin bound, x i = 1 := by
          intro i
          rcases PEqualNP.Outside.L_pcx_448_aux.zmod2_eq_zero_or_one (x i) with h0 | h1
          · exact (hall i h0).elim
          · exact h1
        have hP1 : (∏ i ∈ S1, x i) = 1 := Finset.prod_eq_one (fun i _ => hx1 i)
        have hP2 : (∏ i ∈ S2, x i) = 1 := Finset.prod_eq_one (fun i _ => hx1 i)
        rw [hP1, hP2, PEqualNP.Outside.L_pcx_448_aux.zmod2_add_self, mul_zero, add_zero] at hu
        exact one_ne_zero hu
      · rintro ⟨i, hi⟩
        by_cases hlt : i.val < d + 1
        · refine ⟨0, ?_⟩
          rw [hev 0, zero_mul, add_zero]
          exact Finset.prod_eq_zero (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hlt⟩) hi
        · refine ⟨∏ j ∈ S1, x j, ?_⟩
          rw [hev]
          have hP2 : (∏ j ∈ S2, x j) = 0 :=
            Finset.prod_eq_zero (Finset.mem_filter.mpr ⟨Finset.mem_univ i, by omega⟩) hi
          rw [hP2, add_zero, mul_one, PEqualNP.Outside.L_pcx_448_aux.zmod2_add_self]
    refine ⟨f, hf_deg, hf_eval, ?_⟩
    intro G hG
    let ones : Fin bound → K := fun _ => 1
    have hones_no : ¬ (∃ i : Fin bound, ones i = 0) := by
      rintro ⟨i, hi⟩; exact one_ne_zero hi
    have hnot_all : ¬ (∀ p ∈ G, MvPolynomial.eval ones p = 0) := by
      intro hall
      exact hones_no ((hf_eval ones).mp ((hG ones).mpr hall))
    push_neg at hnot_all
    rcases hnot_all with ⟨p, hpG, hp_ne⟩
    have hp_ones : MvPolynomial.eval ones p = 1 := by
      rcases PEqualNP.Outside.L_pcx_448_aux.zmod2_eq_zero_or_one (MvPolynomial.eval ones p) with h0 | h1
      · exact (hp_ne h0).elim
      · exact h1
    have hp_other : ∀ x : Fin bound → K, x ≠ ones → MvPolynomial.eval x p = 0 := by
      intro x hx
      have hex0 : ∃ i : Fin bound, x i = 0 := by
        by_contra hall
        push_neg at hall
        apply hx
        ext i
        rcases PEqualNP.Outside.L_pcx_448_aux.zmod2_eq_zero_or_one (x i) with h0 | h1
        · exact (hall i h0).elim
        · exact h1
      exact (hG x).mp ((hf_eval x).mpr hex0) p hpG
    have hsum1 : (∑ x : Fin bound → K, MvPolynomial.eval x p) = 1 := by
      rw [Finset.sum_eq_single ones]
      · exact hp_ones
      · intro x _ hx; exact hp_other x hx
      · intro hnot; exact (hnot (Finset.mem_univ ones)).elim
    refine ⟨p, hpG, ?_⟩
    by_contra hlt
    push_neg at hlt
    have hsum0 := PEqualNP.Outside.L_pcx_448_aux.sum_eval_eq_zero_of_lt p hlt
    rw [hsum1] at hsum0
    exact one_ne_zero hsum0
