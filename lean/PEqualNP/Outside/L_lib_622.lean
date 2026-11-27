import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_622

open Finset Classical

theorem rank_ge {K : Type} [Field K] {n k : ℕ} (M : Matrix (Fin n) (Fin n) K)
    (hd : ∀ i, M i i ≠ 0) (f : Fin k → Fin n) (hf : ∀ a b, a < b → M (f b) (f a) = 0) :
    k ≤ M.rank := by
  have h1 : (M.submatrix f f).rank ≤ M.rank := Matrix.rank_submatrix_le M f f
  have hdet : (M.submatrix f f).det ≠ 0 := by
    rw [Matrix.det_of_isUpperTriangular (M := M.submatrix f f) (fun i j hij => hf j i hij)]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hd (f i))
  have h2 : (M.submatrix f f).rank = k := by
    rw [Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).mpr hdet.isUnit)]
    simp
  omega

noncomputable def gr {K : Type} [Field K] {n : ℕ} (N : Matrix (Fin n) (Fin n) K) :
    SimpleGraph (Fin n) :=
  SimpleGraph.fromRel (fun x y : Fin n => x < y ∧ N y x ≠ 0)

theorem gr_cf {K : Type} [Field K] {n p : ℕ} (N : Matrix (Fin n) (Fin n) K)
    (hd : ∀ i, N i i ≠ 0) (hr : N.rank ≤ p) : (gr N)ᶜ.CliqueFree (p + 1) := by
  intro S hS
  have hc := hS.card_eq
  have := rank_ge N hd (fun a => S.orderEmbOfFin hc a) (fun a b hab => by
    by_contra hne
    have hfab : S.orderEmbOfFin hc a < S.orderEmbOfFin hc b := (S.orderEmbOfFin hc).strictMono hab
    have hadj := hS.isClique (S.orderEmbOfFin_mem hc a) (S.orderEmbOfFin_mem hc b) hfab.ne
    rw [SimpleGraph.compl_adj] at hadj
    exact hadj.2 (by rw [gr, SimpleGraph.fromRel_adj]; exact ⟨hfab.ne, Or.inl ⟨hfab, hne⟩⟩))
  omega

theorem size_mod (n p : ℕ) (hp : 0 < p) (t : ℕ) (ht : t < p) :
    (univ.filter (fun v : Fin n => (v : ℕ) % p = t)).card
      = n / p + if t < n % p then 1 else 0 := by
  have h := Nat.count_modEq_card (b := n) hp t
  rw [Nat.mod_eq_of_lt ht] at h
  rw [← h, Nat.count_eq_card_filter_range, ← Finset.card_map Fin.valEmbedding]
  congr 1
  ext x
  simp only [mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply, mem_range,
    Nat.ModEq, Nat.mod_eq_of_lt ht]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a.2, ha⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, h, rfl⟩

theorem pairs_eq (n p : ℕ) (hp : 0 < p) (cell : Fin n → Fin p)
    (hs : ∀ t : Fin p, n / p ≤ (univ.filter (fun i => cell i = t)).card ∧
      (univ.filter (fun i => cell i = t)).card ≤ (n + p - 1) / p) :
    (univ.filter (fun x : Fin n × Fin n => cell x.1 = cell x.2)).card
      = (p - n % p) * (n / p) ^ 2 + n % p * (n / p + 1) ^ 2 := by
  have h1 : (univ.filter (fun x : Fin n × Fin n => cell x.1 = cell x.2)).card
      = ∑ t : Fin p, (univ.filter (fun i => cell i = t)).card ^ 2 := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun x : Fin n × Fin n => cell x.1)
      (t := univ) (fun _ _ => mem_univ _)]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [sq, ← Finset.card_product]
    congr 1
    ext ⟨x, y⟩
    simp only [mem_filter, mem_univ, true_and, mem_product]
    constructor
    · rintro ⟨h, h'⟩
      exact ⟨h', h ▸ h'⟩
    · rintro ⟨h, h'⟩
      exact ⟨h.trans h'.symm, h⟩
  have h2 : ∑ t : Fin p, (univ.filter (fun i => cell i = t)).card = n := by
    rw [← Finset.card_eq_sum_card_fiberwise (f := cell) (s := univ)
      (t := univ) (fun _ _ => mem_univ _)]
    simp
  have hn := Nat.div_add_mod n p
  have hu := Nat.mod_lt n hp
  generalize n / p = q at *
  generalize n % p = u at *
  have hceil : (n + p - 1) / p ≤ q + 1 := by
    have : (n + p - 1) / p < q + 2 := by
      rw [Nat.div_lt_iff_lt_mul hp]
      have : (q + 2) * p = p * q + 2 * p := by ring
      omega
    omega
  have h3 : ∀ t : Fin p, (univ.filter (fun i => cell i = t)).card ^ 2 + q * (q + 1)
      = (2 * q + 1) * (univ.filter (fun i => cell i = t)).card := by
    intro t
    have := hs t
    have h' : (univ.filter (fun i => cell i = t)).card = q ∨
        (univ.filter (fun i => cell i = t)).card = q + 1 := by omega
    rcases h' with h' | h' <;> rw [h'] <;> ring
  have h4 : ∑ t : Fin p, (univ.filter (fun i => cell i = t)).card ^ 2 + p * (q * (q + 1))
      = (2 * q + 1) * ∑ t : Fin p, (univ.filter (fun i => cell i = t)).card := by
    rw [Finset.mul_sum, ← Finset.sum_congr rfl (fun t _ => h3 t), Finset.sum_add_distrib]
    simp
  rw [h2] at h4
  rw [h1]
  obtain ⟨d, rfl⟩ : ∃ d, p = u + d := ⟨p - u, by omega⟩
  have h5 : u + d - u = d := by omega
  rw [h5]
  subst hn
  nlinarith

noncomputable def W {K : Type} [Field K] {n : ℕ} (N : Matrix (Fin n) (Fin n) K) : ℕ :=
  (univ.filter (fun x : Fin n × Fin n => N x.1 x.2 ≠ 0)).card

noncomputable def L {K : Type} [Field K] {n : ℕ} (N : Matrix (Fin n) (Fin n) K) : ℕ :=
  (univ.filter (fun x : Fin n × Fin n => x.1 < x.2 ∧ N x.2 x.1 ≠ 0)).card

theorem swapcard {n : ℕ} (q : Fin n × Fin n → Prop) :
    (univ.filter q).card = (univ.filter (fun x : Fin n × Fin n => q x.swap)).card := by
  refine Finset.card_equiv (Equiv.prodComm _ _) (fun i => ?_)
  simp

theorem diagcard (n : ℕ) : (univ.filter (fun x : Fin n × Fin n => x.1 = x.2)).card = n := by
  have : univ.filter (fun x : Fin n × Fin n => x.1 = x.2) = (univ : Finset (Fin n)).diag := by
    ext ⟨x, y⟩
    simp
  rw [this]
  simp

theorem weight_eq {K : Type} [Field K] {n : ℕ} (N : Matrix (Fin n) (Fin n) K)
    (hd : ∀ i, N i i ≠ 0) : W N = n + L N + L N.transpose := by
  have hT : L N.transpose
      = (univ.filter (fun x : Fin n × Fin n => x.1 < x.2 ∧ N x.1 x.2 ≠ 0)).card := rfl
  rw [hT]
  unfold W L
  rw [← Finset.card_filter_add_card_filter_not (fun x : Fin n × Fin n => x.1 = x.2),
    Finset.filter_filter, Finset.filter_filter]
  have e1 : univ.filter (fun x : Fin n × Fin n => N x.1 x.2 ≠ 0 ∧ x.1 = x.2)
      = univ.filter (fun x : Fin n × Fin n => x.1 = x.2) := by
    ext ⟨x, y⟩
    simp only [mem_filter, mem_univ, true_and, and_iff_right_iff_imp]
    rintro rfl
    exact hd x
  rw [e1, diagcard,
    ← Finset.card_filter_add_card_filter_not (fun x : Fin n × Fin n => x.1 < x.2),
    Finset.filter_filter, Finset.filter_filter]
  have e2 : univ.filter (fun x : Fin n × Fin n => (N x.1 x.2 ≠ 0 ∧ ¬ x.1 = x.2) ∧ x.1 < x.2)
      = univ.filter (fun x : Fin n × Fin n => x.1 < x.2 ∧ N x.1 x.2 ≠ 0) := by
    ext ⟨x, y⟩
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨⟨h, -⟩, h'⟩
      exact ⟨h', h⟩
    · rintro ⟨h, h'⟩
      exact ⟨⟨h', h.ne⟩, h⟩
  have e3 : (univ.filter (fun x : Fin n × Fin n =>
      (N x.1 x.2 ≠ 0 ∧ ¬ x.1 = x.2) ∧ ¬ x.1 < x.2)).card
      = (univ.filter (fun x : Fin n × Fin n => x.1 < x.2 ∧ N x.2 x.1 ≠ 0)).card := by
    convert (swapcard (fun x : Fin n × Fin n => x.1 < x.2 ∧ N x.2 x.1 ≠ 0)).symm using 2
    · ext ⟨x, y⟩
      simp only [mem_filter, mem_univ, true_and, Prod.swap]
      constructor
      · rintro ⟨⟨h, h1⟩, h'⟩
        exact ⟨lt_of_le_of_ne (not_lt.mp h') (Ne.symm h1), h⟩
      · rintro ⟨h, h'⟩
        exact ⟨⟨h', h.ne'⟩, not_lt.mpr h.le⟩
    · ext x
      simp only [mem_filter]
  rw [e2, e3]
  ring

theorem gr_pairs {K : Type} [Field K] {n : ℕ} (N : Matrix (Fin n) (Fin n) K) :
    (univ.filter (fun x : Fin n × Fin n => (gr N).Adj x.1 x.2)).card = 2 * L N := by
  unfold L
  rw [← Finset.card_filter_add_card_filter_not (fun x : Fin n × Fin n => x.1 < x.2),
    Finset.filter_filter, Finset.filter_filter]
  have e2 : univ.filter (fun x : Fin n × Fin n => (gr N).Adj x.1 x.2 ∧ x.1 < x.2)
      = univ.filter (fun x : Fin n × Fin n => x.1 < x.2 ∧ N x.2 x.1 ≠ 0) := by
    ext ⟨x, y⟩
    simp only [mem_filter, mem_univ, true_and, gr, SimpleGraph.fromRel_adj]
    constructor
    · rintro ⟨⟨-, h | h⟩, h'⟩
      · exact h
      · exact absurd h.1 (not_lt.mpr h'.le)
    · rintro ⟨h, h'⟩
      exact ⟨⟨h.ne, Or.inl ⟨h, h'⟩⟩, h⟩
  have e3 : (univ.filter (fun x : Fin n × Fin n => (gr N).Adj x.1 x.2 ∧ ¬ x.1 < x.2)).card
      = (univ.filter (fun x : Fin n × Fin n => x.1 < x.2 ∧ N x.2 x.1 ≠ 0)).card := by
    convert (swapcard (fun x : Fin n × Fin n => x.1 < x.2 ∧ N x.2 x.1 ≠ 0)).symm using 2
    · ext ⟨x, y⟩
      simp only [mem_filter, mem_univ, true_and, Prod.swap, gr, SimpleGraph.fromRel_adj]
      constructor
      · rintro ⟨⟨-, h | h⟩, h'⟩
        · exact absurd h.1 h'
        · exact h
      · rintro ⟨h, h'⟩
        exact ⟨⟨h.ne', Or.inr ⟨h, h'⟩⟩, not_lt.mpr h.le⟩
    · ext x
      simp only [mem_filter]
  rw [e2, e3]
  ring

theorem compl_pairs {n : ℕ} (G : SimpleGraph (Fin n)) :
    (univ.filter (fun x : Fin n × Fin n => G.Adj x.1 x.2)).card
      + (univ.filter (fun x : Fin n × Fin n => Gᶜ.Adj x.1 x.2)).card + n = n * n := by
  have h := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin n × Fin n)))
    (fun x : Fin n × Fin n => G.Adj x.1 x.2)
  rw [← Finset.card_filter_add_card_filter_not (s := univ.filter
    (fun x : Fin n × Fin n => ¬ G.Adj x.1 x.2)) (fun x : Fin n × Fin n => x.1 = x.2),
    Finset.filter_filter, Finset.filter_filter] at h
  have e1 : univ.filter (fun x : Fin n × Fin n => ¬ G.Adj x.1 x.2 ∧ x.1 = x.2)
      = univ.filter (fun x : Fin n × Fin n => x.1 = x.2) := by
    ext ⟨x, y⟩
    simp only [mem_filter, mem_univ, true_and, and_iff_right_iff_imp]
    rintro rfl
    exact G.irrefl
  have e2 : univ.filter (fun x : Fin n × Fin n => ¬ G.Adj x.1 x.2 ∧ ¬ x.1 = x.2)
      = univ.filter (fun x : Fin n × Fin n => Gᶜ.Adj x.1 x.2) := by
    ext ⟨x, y⟩
    simp only [mem_filter, mem_univ, true_and, SimpleGraph.compl_adj]
    tauto
  rw [e1, e2, diagcard] at h
  simp only [card_univ, Fintype.card_prod, Fintype.card_fin] at h
  omega

theorem twoE {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    2 * G.edgeFinset.card = (univ.filter (fun x : Fin n × Fin n => G.Adj x.1 x.2)).card := by
  rw [SimpleGraph.two_mul_card_edgeFinset]

theorem turan_sizes (n p : ℕ) (hp : 0 < p) (t : Fin p) :
    n / p ≤ (univ.filter (fun i : Fin n => (⟨(i : ℕ) % p, Nat.mod_lt _ hp⟩ : Fin p) = t)).card ∧
    (univ.filter (fun i : Fin n => (⟨(i : ℕ) % p, Nat.mod_lt _ hp⟩ : Fin p) = t)).card
      ≤ (n + p - 1) / p := by
  have e : univ.filter (fun i : Fin n => (⟨(i : ℕ) % p, Nat.mod_lt _ hp⟩ : Fin p) = t)
      = univ.filter (fun v : Fin n => (v : ℕ) % p = t) := by
    ext x
    simp [Fin.ext_iff]
  rw [e, size_mod n p hp t t.2]
  have hn := Nat.div_add_mod n p
  have hu := Nat.mod_lt n hp
  generalize n / p = q at *
  generalize n % p = u at *
  refine ⟨Nat.le_add_right _ _, ?_⟩
  rw [Nat.le_div_iff_mul_le hp]
  split_ifs with h
  · have : (q + 1) * p = p * q + p := by ring
    omega
  · have : (q + 0) * p = p * q := by ring
    omega

theorem turan_pairs (n p : ℕ) (hp : 0 < p) :
    (univ.filter (fun x : Fin n × Fin n => (SimpleGraph.turanGraph n p).Adj x.1 x.2)).card
      + ((p - n % p) * (n / p) ^ 2 + n % p * (n / p + 1) ^ 2) = n * n := by
  rw [← pairs_eq n p hp (fun i => ⟨(i : ℕ) % p, Nat.mod_lt _ hp⟩) (turan_sizes n p hp)]
  have h := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin n × Fin n)))
    (fun x : Fin n × Fin n => (SimpleGraph.turanGraph n p).Adj x.1 x.2)
  simp only [card_univ, Fintype.card_prod, Fintype.card_fin] at h
  rw [← h]
  congr 2
  ext ⟨x, y⟩
  simp [SimpleGraph.turanGraph_adj, Fin.ext_iff]

theorem key {K : Type} [Field K] {n p : ℕ} (hp : 0 < p) (N : Matrix (Fin n) (Fin n) K)
    (hd : ∀ i, N i i ≠ 0) (hr : N.rank ≤ p) :
    (p - n % p) * (n / p) ^ 2 + n % p * (n / p + 1) ^ 2 ≤ 2 * L N + n ∧
    ((p - n % p) * (n / p) ^ 2 + n % p * (n / p + 1) ^ 2 = 2 * L N + n →
      (gr N)ᶜ.IsTuranMaximal p) := by
  have cf := gr_cf N hd hr
  have T := SimpleGraph.isTuranMaximal_turanGraph (n := n) hp
  have hle : (gr N)ᶜ.edgeFinset.card ≤ (SimpleGraph.turanGraph n p).edgeFinset.card := T.2 cf
  have h1 := twoE (gr N)ᶜ
  have h2 := twoE (SimpleGraph.turanGraph n p)
  have h3 := compl_pairs (gr N)
  have h4 := turan_pairs n p hp
  have h5 := gr_pairs N
  refine ⟨by omega, fun heq => ?_⟩
  have h6 : (gr N)ᶜ.edgeFinset.card = (SimpleGraph.turanGraph n p).edgeFinset.card := by omega
  refine ⟨cf, fun G' _ cf' => ?_⟩
  rw [h6]
  exact T.2 cf'

theorem mainbound {K : Type} [Field K] {n p : ℕ} (hp : 0 < p) (N : Matrix (Fin n) (Fin n) K)
    (hd : ∀ i, N i i ≠ 0) (hr : N.rank ≤ p) :
    (p - n % p) * (n / p) ^ 2 + n % p * (n / p + 1) ^ 2 ≤ W N ∧
    (W N = (p - n % p) * (n / p) ^ 2 + n % p * (n / p + 1) ^ 2 →
      (p - n % p) * (n / p) ^ 2 + n % p * (n / p + 1) ^ 2 = 2 * L N + n) := by
  have h1 := (key hp N hd hr).1
  have h2 := (key hp N.transpose (fun i => hd i) (by rw [Matrix.rank_transpose]; exact hr)).1
  have h3 := weight_eq N hd
  constructor <;> omega

theorem Lconst {K : Type} [Field K] {n p : ℕ} (hp : 0 < p) (M : Matrix (Fin n) (Fin n) K)
    (hd : ∀ i, M i i ≠ 0) (hr : M.rank ≤ p)
    (hW : W M = (p - n % p) * (n / p) ^ 2 + n % p * (n / p + 1) ^ 2) (σ : Equiv.Perm (Fin n)) :
    (p - n % p) * (n / p) ^ 2 + n % p * (n / p + 1) ^ 2 = 2 * L (M.submatrix σ σ) + n := by
  refine (mainbound hp (M.submatrix σ σ) (fun i => hd (σ i)) ?_).2 ?_
  · rw [Matrix.rank_submatrix]
    exact hr
  · rw [← hW]
    unfold W
    refine Finset.card_equiv (Equiv.prodCongr σ σ) (fun i => ?_)
    rw [mem_filter, mem_filter]
    simp

theorem swap_order {n : ℕ} (a b x y : Fin n) (hab : (b : ℕ) = a + 1) :
    (¬(x = a ∧ y = b) → (x < y ↔ ¬(Equiv.swap a b x = a ∧ Equiv.swap a b y = b) ∧
      Equiv.swap a b x < Equiv.swap a b y)) ∧
    (Equiv.swap a b x < Equiv.swap a b y → ¬(x = a ∧ y = b)) := by
  rw [Equiv.swap_apply_def, Equiv.swap_apply_def]
  split_ifs with h1 h2 h3 h4 <;> simp only [Fin.lt_def, Fin.ext_iff] at * <;>
    (try simp only [and_self, not_true_eq_false, false_and, iff_false] at *) <;> omega

theorem swapL {K : Type} [Field K] {n : ℕ} (N : Matrix (Fin n) (Fin n) K) (a b : Fin n)
    (hab : (b : ℕ) = a + 1) (h1 : N b a ≠ 0) (h2 : N a b = 0) :
    L (N.submatrix (Equiv.swap a b) (Equiv.swap a b)) + 1 = L N := by
  unfold L
  have e : (univ.filter (fun x : Fin n × Fin n => x.1 < x.2 ∧
      N.submatrix (Equiv.swap a b) (Equiv.swap a b) x.2 x.1 ≠ 0)).card
      = ((univ.filter (fun x : Fin n × Fin n => x.1 < x.2 ∧ N x.2 x.1 ≠ 0)).erase (a, b)).card := by
    refine Finset.card_equiv (Equiv.prodCongr (Equiv.swap a b) (Equiv.swap a b)) (fun ⟨x, y⟩ => ?_)
    rw [mem_filter, mem_erase, mem_filter]
    simp only [mem_univ, true_and, Matrix.submatrix_apply, Equiv.prodCongr_apply, Prod.map,
      ne_eq, Prod.mk.injEq]
    have so := swap_order a b x y hab
    constructor
    · rintro ⟨hlt, hP⟩
      have hne : ¬(x = a ∧ y = b) := by
        rintro ⟨rfl, rfl⟩
        rw [Equiv.swap_apply_left, Equiv.swap_apply_right] at hP
        exact hP h2
      exact ⟨((so.1 hne).mp hlt).1, ((so.1 hne).mp hlt).2, hP⟩
    · rintro ⟨h1', h2', hP⟩
      exact ⟨(so.1 (so.2 h2')).mpr ⟨h1', h2'⟩, hP⟩
  have hmem : (a, b) ∈ univ.filter (fun x : Fin n × Fin n => x.1 < x.2 ∧ N x.2 x.1 ≠ 0) := by
    rw [mem_filter]
    exact ⟨mem_univ _, (Fin.lt_def.mpr (by omega) : a < b), h1⟩
  rw [e, Finset.card_erase_of_mem hmem]
  have := Finset.card_pos.mpr ⟨_, hmem⟩
  omega

theorem symm_supp {K : Type} [Field K] {n c : ℕ} (M : Matrix (Fin n) (Fin n) K)
    (hL : ∀ σ : Equiv.Perm (Fin n), c = 2 * L (M.submatrix σ σ) + n) (i j : Fin n)
    (hij : i ≠ j) (h1 : M i j ≠ 0) : M j i ≠ 0 := by
  intro h2
  have hn : 2 ≤ n := by
    have := i.2
    have := j.2
    have : (i : ℕ) ≠ j := Fin.val_ne_of_ne hij
    omega
  obtain ⟨a, ha⟩ : ∃ a : Fin n, (a : ℕ) = 0 := ⟨⟨0, by omega⟩, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : Fin n, (b : ℕ) = 1 := ⟨⟨1, by omega⟩, rfl⟩
  have hab : a ≠ b := by
    intro h
    rw [h] at ha
    omega
  obtain ⟨σ, hσa, hσb⟩ : ∃ σ : Equiv.Perm (Fin n), σ a = j ∧ σ b = i := by
    have hne : a ≠ Equiv.swap a j i := by
      intro h
      have h' := congrArg (Equiv.swap a j) h
      rw [Equiv.swap_apply_left, Equiv.swap_apply_self] at h'
      exact hij h'.symm
    refine ⟨Equiv.swap a j * Equiv.swap b (Equiv.swap a j i), ?_, ?_⟩
    · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hab hne, Equiv.swap_apply_left]
    · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_self]
  have h := swapL (M.submatrix σ σ) a b (by omega)
    (by rw [Matrix.submatrix_apply, hσa, hσb]; exact h1)
    (by rw [Matrix.submatrix_apply, hσa, hσb]; exact h2)
  have e1 := hL σ
  have e2 : c = 2 * L ((M.submatrix σ σ).submatrix (Equiv.swap a b) (Equiv.swap a b)) + n :=
    hL (σ * Equiv.swap a b)
  omega

theorem cells {K : Type} [Field K] {n p m : ℕ} (hp : 0 < p) (hm : m = n)
    (M : Matrix (Fin n) (Fin n) K) (hd : ∀ i, M i i ≠ 0)
    (hsym : ∀ i j, i ≠ j → M i j ≠ 0 → M j i ≠ 0)
    (φ : (gr M)ᶜ ≃g SimpleGraph.turanGraph m p) :
    ∃ cell : Fin n → Fin p, (∀ i j, M i j ≠ 0 ↔ cell i = cell j) ∧
      ∀ t : Fin p, n / p ≤ (univ.filter (fun i => cell i = t)).card ∧
        (univ.filter (fun i => cell i = t)).card ≤ (n + p - 1) / p := by
  subst hm
  refine ⟨fun i => ⟨(φ i : ℕ) % p, Nat.mod_lt _ hp⟩, fun i j => ?_, fun t => ?_⟩
  · by_cases hij : i = j
    · subst hij
      simp [hd]
    · have h := φ.map_adj_iff (v := i) (w := j)
      rw [SimpleGraph.turanGraph_adj, SimpleGraph.compl_adj] at h
      simp only [gr, SimpleGraph.fromRel_adj] at h
      simp only [Fin.mk.injEq]
      constructor
      · intro hM
        by_contra hc
        refine (h.mp hc).2 ⟨hij, ?_⟩
        rcases lt_or_gt_of_ne hij with h' | h'
        · exact Or.inl ⟨h', hsym i j hij hM⟩
        · exact Or.inr ⟨h', hM⟩
      · intro hc hM0
        have hadj : i ≠ j ∧ (i < j ∧ M j i ≠ 0 ∨ j < i ∧ M i j ≠ 0) := by
          by_contra hna
          exact (h.mpr ⟨hij, hna⟩) hc
        rcases hadj.2 with ⟨_, h'⟩ | ⟨_, h'⟩
        · exact hsym j i (Ne.symm hij) h' hM0
        · exact h' hM0
  · have e : (univ.filter (fun i : Fin m => (⟨(φ i : ℕ) % p, Nat.mod_lt _ hp⟩ : Fin p) = t)).card
        = (univ.filter (fun i : Fin m => (⟨(i : ℕ) % p, Nat.mod_lt _ hp⟩ : Fin p) = t)).card := by
      refine Finset.card_equiv φ.toEquiv (fun i => ?_)
      rw [mem_filter, mem_filter]
      simp
    rw [e]
    exact turan_sizes m p hp t

theorem exists_mat (K : Type) [Field K] (n p : ℕ) (hp : 0 < p) :
    ∃ M : Matrix (Fin n) (Fin n) K, (∀ i, M i i ≠ 0) ∧ M.rank ≤ p ∧
      W M = (p - n % p) * (n / p) ^ 2 + n % p * (n / p + 1) ^ 2 := by
  obtain ⟨A, hAdef⟩ : ∃ A : Matrix (Fin n) (Fin p) K, ∀ i t, A i t =
      if (⟨(i : ℕ) % p, Nat.mod_lt _ hp⟩ : Fin p) = t then (1 : K) else 0 :=
    ⟨Matrix.of fun i t => if (⟨(i : ℕ) % p, Nat.mod_lt _ hp⟩ : Fin p) = t then (1 : K) else 0,
      fun _ _ => rfl⟩
  have hA : ∀ i j : Fin n, (A * A.transpose) i j
      = if (⟨(i : ℕ) % p, Nat.mod_lt _ hp⟩ : Fin p) = ⟨(j : ℕ) % p, Nat.mod_lt _ hp⟩
        then 1 else 0 := by
    intro i j
    simp [Matrix.mul_apply, hAdef]
  refine ⟨A * A.transpose, fun i => ?_, (Matrix.rank_mul_le_left A A.transpose).trans
    ((Matrix.rank_le_card_width A).trans (le_of_eq (Fintype.card_fin p))), ?_⟩
  · rw [hA]
    simp
  · unfold W
    rw [← pairs_eq n p hp (fun i => ⟨(i : ℕ) % p, Nat.mod_lt _ hp⟩) (turan_sizes n p hp)]
    congr 1
    ext x
    rw [mem_filter, mem_filter, hA]
    simp

theorem main (K : Type) [Field K] (n p : ℕ) (hp : 0 < p) :
    (∀ M : Matrix (Fin n) (Fin n) K, (∀ i, M i i ≠ 0) → M.rank ≤ p →
      (p - n % p) * (n / p) ^ 2 + n % p * (n / p + 1) ^ 2 ≤ W M ∧
      (W M = (p - n % p) * (n / p) ^ 2 + n % p * (n / p + 1) ^ 2 ↔
        ∃ cell : Fin n → Fin p, (∀ i j, M i j ≠ 0 ↔ cell i = cell j) ∧
          ∀ t : Fin p, n / p ≤ (univ.filter (fun i => cell i = t)).card ∧
            (univ.filter (fun i => cell i = t)).card ≤ (n + p - 1) / p)) ∧
    ∃ M : Matrix (Fin n) (Fin n) K, (∀ i, M i i ≠ 0) ∧ M.rank ≤ p ∧
      W M = (p - n % p) * (n / p) ^ 2 + n % p * (n / p + 1) ^ 2 := by
  refine ⟨fun M hd hr => ?_, exists_mat K n p hp⟩
  have hb := mainbound hp M hd hr
  refine ⟨hb.1, ⟨fun hW => ?_, ?_⟩⟩
  · have hL := Lconst hp M hd hr hW
    have hsym := fun i j hij h => symm_supp M hL i j hij h
    have hT := (key hp M hd hr).2 (hL 1)
    obtain ⟨φ⟩ := hT.nonempty_iso_turanGraph
    exact cells hp (Fintype.card_fin n) M hd hsym φ
  · rintro ⟨cell, hc, hs⟩
    unfold W
    rw [← pairs_eq n p hp cell hs]
    congr 1
    ext x
    rw [mem_filter, mem_filter]
    simp only [mem_univ, true_and]
    exact hc _ _

end PEqualNP.Outside.L_lib_622

theorem PEqualNP.Outside.L_lib_622 : (∀ (K : Type) [Field K] (n p : ℕ), 0 < p →
  let weight := fun M : Matrix (Fin n) (Fin n) K =>
    (@Finset.filter _ (fun v : Fin n × Fin n => M v.1 v.2 ≠ 0) (Classical.decPred _) Finset.univ).card
  let q := n / p
  let u := n % p
  let minimum := (p-u)*q^2 + u*(q+1)^2
  (∀ M : Matrix (Fin n) (Fin n) K, (∀ i, M i i ≠ 0) → M.rank ≤ p →
    minimum ≤ weight M ∧ (weight M = minimum ↔
      ∃ cell : Fin n → Fin p,
        (∀ i j, M i j ≠ 0 ↔ cell i = cell j) ∧
        ∀ t : Fin p, let size := (Finset.univ.filter (fun i => cell i = t)).card
          q ≤ size ∧ size ≤ (n+p-1)/p)) ∧
  ∃ M : Matrix (Fin n) (Fin n) K, (∀ i, M i i ≠ 0) ∧ M.rank ≤ p ∧ weight M = minimum) := by
  intro K _ n p hp weight q u minimum
  have hw : weight = PEqualNP.Outside.L_lib_622.W := by
    funext M
    simp only [weight, PEqualNP.Outside.L_lib_622.W]
    congr
  rw [hw]
  exact PEqualNP.Outside.L_lib_622.main K n p hp
