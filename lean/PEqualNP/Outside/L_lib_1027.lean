import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1027_aux

open Finset


def GC (s : ℕ) {ι α : Type} [Fintype ι] [DecidableEq α] (S : ι → Finset α) (w : ι → ℝ) : Prop :=
  (∀ i, (S i).card = s ∧ 0 < w i) ∧ ∀ y, (∑ i, if y ∈ S i then w i else 0) = 1

def HC (s : ℕ) (α : Type) [DecidableEq α] (m : ℕ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι), Fintype.card ι = m ∧ ∃ (S : ι → Finset α) (w : ι → ℝ), GC s S w

section structure_lemmas

variable {s : ℕ} {ι α : Type} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]
  {S : ι → Finset α} {w : ι → ℝ}

lemma term_nonneg (h : GC s S w) (y : α) (j : ι) : 0 ≤ (if y ∈ S j then w j else 0) := by
  split_ifs
  · exact (h.1 j).2.le
  · exact le_rfl

lemma nonempty_set (h : GC s S w) (hs : 0 < s) (i : ι) : (S i).Nonempty := by
  rw [← Finset.card_pos, (h.1 i).1]; exact hs

lemma w_le (h : GC s S w) (hs : 0 < s) (i : ι) : w i ≤ 1 := by
  obtain ⟨y, hy⟩ := nonempty_set h hs i
  rw [← h.2 y]
  have := Finset.single_le_sum (f := fun j => if y ∈ S j then w j else 0)
    (fun j _ => term_nonneg h y j) (Finset.mem_univ i)
  simpa [hy] using this

lemma pair_le (h : GC s S w) {i j : ι} (hij : i ≠ j) {y : α} (hi : y ∈ S i) (hj : y ∈ S j) :
    w i + w j ≤ 1 := by
  rw [← h.2 y]
  have := Finset.sum_le_sum_of_subset_of_nonneg (f := fun k => if y ∈ S k then w k else 0)
    (Finset.subset_univ {i, j}) (fun k _ _ => term_nonneg h y k)
  rw [Finset.sum_pair hij] at this
  simpa [hi, hj] using this

lemma iso_iff (h : GC s S w) (hs : 0 < s) (i : ι) :
    w i = 1 ↔ ∀ j, i ≠ j → Disjoint (S i) (S j) := by
  constructor
  · intro h1 j hij
    rw [Finset.disjoint_left]
    intro y hy hy'
    have := pair_le h hij hy hy'
    linarith [(h.1 j).2]
  · intro hd
    obtain ⟨y, hy⟩ := nonempty_set h hs i
    rw [← h.2 y, Finset.sum_eq_single i]
    · simp [hy]
    · intro j _ hji
      have : y ∉ S j := Finset.disjoint_left.mp (hd j (Ne.symm hji)) hy
      simp [this]
    · simp

lemma noncore_iso (h : GC s S w) (hs : 0 < s) {i : ι} (hi : ¬ w i < 1) :
    ∀ j, i ≠ j → Disjoint (S i) (S j) :=
  (iso_iff h hs i).mp (le_antisymm (w_le h hs i) (not_lt.mp hi))

lemma deg2 (h : GC s S w) (hs : 0 < s) (y : α)
    (hy : y ∈ (univ.filter (fun i => w i < 1)).biUnion S) :
    2 ≤ ((univ.filter (fun i => w i < 1)).filter (fun i => y ∈ S i)).card := by
  simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and] at hy
  obtain ⟨i, hi1, hyi⟩ := hy
  have hex : ∃ j, j ≠ i ∧ y ∈ S j := by
    by_contra hno
    push Not at hno
    have := h.2 y
    rw [Finset.sum_eq_single i] at this
    · simp only [hyi, ite_true] at this; linarith
    · intro j _ hji; simp [hno j hji]
    · simp
  obtain ⟨j, hji, hyj⟩ := hex
  have hj1 : w j < 1 := by
    by_contra hc
    exact Finset.disjoint_left.mp (noncore_iso h hs hc i hji) hyj hyi
  have hsub : ({i, j} : Finset ι) ⊆
      (univ.filter (fun i => w i < 1)).filter (fun i => y ∈ S i) := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with hk | hk <;> subst hk <;> simp [*]
  calc 2 = ({i, j} : Finset ι).card := (Finset.card_pair (Ne.symm hji)).symm
    _ ≤ _ := Finset.card_le_card hsub

lemma covered (h : GC s S w) (y : α) : ∃ i, y ∈ S i := by
  by_contra hno
  push Not at hno
  have := h.2 y
  simp [hno] at this

lemma count_points (h : GC s S w) (hs : 0 < s) :
    Fintype.card α = (univ.filter (fun i => ¬ w i < 1)).card * s +
      ((univ.filter (fun i => w i < 1)).biUnion S).card := by
  set N := univ.filter (fun i => ¬ w i < 1)
  set C := univ.filter (fun i => w i < 1)
  have hU : (univ : Finset α) = N.biUnion S ∪ C.biUnion S := by
    ext y
    simp only [Finset.mem_univ, true_iff, Finset.mem_union, Finset.mem_biUnion]
    obtain ⟨i, hi⟩ := covered h y
    by_cases hw : w i < 1
    · exact Or.inr ⟨i, by simp [C, hw], hi⟩
    · exact Or.inl ⟨i, by simp [N]; exact not_lt.mp hw, hi⟩
  have hD : Disjoint (N.biUnion S) (C.biUnion S) := by
    rw [Finset.disjoint_biUnion_left]
    intro i hi
    rw [Finset.disjoint_biUnion_right]
    intro j hj
    simp only [N, C, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
    exact noncore_iso h hs hi j (by rintro rfl; exact hi hj)
  have hN : (N.biUnion S).card = N.card * s := by
    rw [Finset.card_biUnion]
    · rw [Finset.sum_congr rfl (fun i _ => (h.1 i).1), Finset.sum_const, smul_eq_mul]
    · intro i hi j _ hij
      simp only [N, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hi
      exact noncore_iso h hs hi j hij
  rw [← Finset.card_univ, hU, Finset.card_union_of_disjoint hD, hN]

lemma core_count (h : GC s S w) :
    ∑ y ∈ (univ.filter (fun i => w i < 1)).biUnion S,
      ((univ.filter (fun i => w i < 1)).filter (fun i => y ∈ S i)).card =
      (univ.filter (fun i => w i < 1)).card * s := by
  set C := univ.filter (fun i => w i < 1)
  have := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := C) (t := C.biUnion S) (r := fun i y => y ∈ S i)
  simp only [Finset.bipartiteAbove, Finset.bipartiteBelow] at this
  rw [← this]
  rw [Finset.sum_congr rfl (g := fun _ => s)]
  · rw [Finset.sum_const, smul_eq_mul]
  · intro i hi
    rw [← (h.1 i).1]
    congr 1
    ext y
    simp only [Finset.mem_filter, Finset.mem_biUnion, and_iff_right_iff_imp]
    exact fun hy => ⟨i, hi, hy⟩

lemma core_sum_ge (h : GC s S w) (hs : 0 < s) :
    2 * ((univ.filter (fun i => w i < 1)).biUnion S).card ≤
      (univ.filter (fun i => w i < 1)).card * s := by
  rw [← core_count h, mul_comm, ← smul_eq_mul, ← Finset.sum_const]
  exact Finset.sum_le_sum (fun y hy => deg2 h hs y hy)

end structure_lemmas

lemma hc_of_fin {s n m : ℕ} {S : Fin m → Finset (Fin n)} {w : Fin m → ℝ} (h : GC s S w) :
    HC s (Fin n) m := ⟨Fin m, inferInstance, Fintype.card_fin m, S, w, h⟩

lemma fin_of_hc {s n m : ℕ} {α : Type} [Fintype α] [DecidableEq α] (h : HC s α m)
    (hα : Fintype.card α = n) : ∃ (S : Fin m → Finset (Fin n)) (w : Fin m → ℝ), GC s S w := by
  obtain ⟨ι, _, hc, S, w, hG⟩ := h
  let eι : ι ≃ Fin m := Fintype.equivFinOfCardEq hc
  let eα : α ≃ Fin n := Fintype.equivFinOfCardEq hα
  refine ⟨fun j => (S (eι.symm j)).map eα.toEmbedding, fun j => w (eι.symm j), ?_, ?_⟩
  · intro j
    simp only [Finset.card_map]
    exact hG.1 _
  · intro y
    simp only [Finset.mem_map_equiv]
    rw [Equiv.sum_comp eι.symm (fun i => if eα.symm y ∈ S i then w i else 0)]
    exact hG.2 _

lemma hc_sum {s m m' : ℕ} {α β : Type} [DecidableEq α] [DecidableEq β]
    (h₁ : HC s α m) (h₂ : HC s β m') : HC s (α ⊕ β) (m + m') := by
  obtain ⟨ι, _, hc, S, w, hG⟩ := h₁
  obtain ⟨ι', _, hc', S', w', hG'⟩ := h₂
  refine ⟨ι ⊕ ι', inferInstance, by rw [Fintype.card_sum, hc, hc'],
    Sum.elim (fun i => (S i).map Function.Embedding.inl)
      (fun j => (S' j).map Function.Embedding.inr), Sum.elim w w', ?_, ?_⟩
  · rintro (i | j)
    · simpa using hG.1 i
    · simpa using hG'.1 j
  · rintro (a | b)
    · rw [Fintype.sum_sum_type]
      simpa using hG.2 a
    · rw [Fintype.sum_sum_type]
      simpa using hG'.2 b

lemma hc_blocks (s k : ℕ) : HC s (Fin k × Fin s) k := by
  refine ⟨Fin k, inferInstance, Fintype.card_fin k, fun i => {i} ×ˢ univ, fun _ => 1, ?_, ?_⟩
  · intro i; simp
  · rintro ⟨a, b⟩
    rw [Finset.sum_eq_single a]
    · simp
    · intro j _ hj; simp [hj]
    · simp

lemma hc_cyclic {s : ℕ} (hs : 0 < s) (G : Type) [AddGroup G] [Fintype G] [DecidableEq G]
    (h : s ≤ Fintype.card G) : HC s G (Fintype.card G) := by
  obtain ⟨D, -, hD⟩ := Finset.exists_subset_card_eq (s := (univ : Finset G)) (n := s)
    (by rwa [Finset.card_univ])
  refine ⟨G, inferInstance, rfl, fun u => D.map (Equiv.addLeft u).toEmbedding,
    fun _ => (1 / s : ℝ), ?_, ?_⟩
  · intro u
    refine ⟨by rw [Finset.card_map, hD], by positivity⟩
  · intro y
    simp only [Finset.mem_map_equiv]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have : (univ.filter (fun u : G => (Equiv.addLeft u).symm y ∈ D)).card = s := by
      rw [← hD]
      apply Finset.card_bij (fun u _ => -u + y)
      · intro u hu
        simpa using hu
      · intro u _ v _ huv
        simpa using huv
      · intro d hd
        refine ⟨y - d, ?_, ?_⟩
        · simp [hd]
        · simp
    rw [this]
    field_simp

lemma hc_three {h : ℕ} : HC (h + h) (Fin 3 × Fin h) 3 := by
  refine ⟨Fin 3, inferInstance, rfl, fun k => (univ.erase k) ×ˢ univ, fun _ => (1 / 2 : ℝ),
    ?_, ?_⟩
  · intro k
    refine ⟨?_, by norm_num⟩
    rw [Finset.card_product, Finset.card_erase_of_mem (Finset.mem_univ _)]
    simp; ring
  · rintro ⟨a, b⟩
    simp only [Finset.mem_product, Finset.mem_erase, Finset.mem_univ, and_true]
    rw [Fin.sum_univ_three]
    fin_cases a <;> simp <;> norm_num

lemma hc_peel {s N m : ℕ} {S : Fin m → Finset (Fin N)} {w : Fin m → ℝ} (h : GC s S w)
    (hs : 0 < s) {i₀ : Fin m} (hi : ¬ w i₀ < 1) :
    HC s {y : Fin N // y ∉ S i₀} (m - 1) := by
  have hd := noncore_iso h hs hi
  refine ⟨{i : Fin m // i ≠ i₀}, inferInstance, ?_, fun i => (S i.1).subtype (fun y => y ∉ S i₀),
    fun i => w i.1, ?_, ?_⟩
  · rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_unique]
  · intro i
    refine ⟨?_, (h.1 i.1).2⟩
    rw [Finset.card_subtype, Finset.filter_true_of_mem, (h.1 i.1).1]
    intro y hy hy'
    exact Finset.disjoint_left.mp (hd i.1 (Ne.symm i.2)) hy' hy
  · intro y
    simp only [Finset.mem_subtype]
    rw [← h.2 y.1]
    rw [← Finset.sum_erase (s := univ) (a := i₀) (by simp [y.2])]
    exact (Finset.sum_subtype (univ.erase i₀) (fun x => by simp)
      (fun i => if y.1 ∈ S i then w i else 0)).symm

lemma card_peel {s N m : ℕ} {S : Fin m → Finset (Fin N)} {w : Fin m → ℝ} (h : GC s S w)
    (i₀ : Fin m) : Fintype.card {y : Fin N // y ∉ S i₀} = N - s := by
  rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe, (h.1 i₀).1]

noncomputable def cost (s n : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ (S : Fin m → Finset (Fin n)) (w : Fin m → ℝ), GC s S w}

lemma cost_le {s n m : ℕ} {S : Fin m → Finset (Fin n)} {w : Fin m → ℝ} (h : GC s S w) :
    cost s n ≤ m := Nat.sInf_le ⟨S, w, h⟩

lemma cost_le_hc {s n m : ℕ} {α : Type} [Fintype α] [DecidableEq α] (h : HC s α m)
    (hα : Fintype.card α = n) : cost s n ≤ m := by
  obtain ⟨S, w, hG⟩ := fin_of_hc h hα
  exact cost_le hG

lemma gen_cost {s n : ℕ} (hs : 0 < s) (hsn : s ≤ n) :
    ∃ m, m ≤ n / s - 1 + (s + n % s) ∧
      ∃ (S : Fin m → Finset (Fin n)) (w : Fin m → ℝ), GC s S w := by
  have : NeZero (s + n % s) := ⟨by omega⟩
  have h := hc_sum (hc_blocks s (n / s - 1))
    (hc_cyclic hs (ZMod (s + n % s)) (by rw [ZMod.card]; omega))
  rw [ZMod.card] at h
  refine ⟨n / s - 1 + (s + n % s), le_rfl, fin_of_hc h ?_⟩
  rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, ZMod.card]
  have hq : 1 ≤ n / s := (Nat.one_le_div_iff hs).mpr hsn
  have e := Nat.div_add_mod n s
  obtain ⟨q', hq'⟩ : ∃ q', n / s = q' + 1 := ⟨n / s - 1, by omega⟩
  rw [hq'] at e ⊢
  simp only [Nat.add_sub_cancel]
  linarith

lemma cost_spec {s n : ℕ} (hs : 0 < s) (hsn : s ≤ n) :
    ∃ (S : Fin (cost s n) → Finset (Fin n)) (w : Fin (cost s n) → ℝ), GC s S w := by
  obtain ⟨m, -, S, w, h⟩ := gen_cost hs hsn
  exact Nat.sInf_mem (s := {m : ℕ | ∃ (S : Fin m → Finset (Fin n)) (w : Fin m → ℝ), GC s S w})
    ⟨m, S, w, h⟩

lemma cost_le_gen {s n : ℕ} (hs : 0 < s) (hsn : s ≤ n) :
    cost s n ≤ n / s - 1 + (s + n % s) := by
  obtain ⟨m, hm, S, w, h⟩ := gen_cost hs hsn
  exact (cost_le h).trans hm

lemma counts {s n m : ℕ} (hs : 0 < s) {S : Fin m → Finset (Fin n)} {w : Fin m → ℝ}
    (h : GC s S w) :
    n = (univ.filter (fun i => ¬ w i < 1)).card * s +
        ((univ.filter (fun i => w i < 1)).biUnion S).card ∧
    2 * ((univ.filter (fun i => w i < 1)).biUnion S).card ≤
        (univ.filter (fun i => w i < 1)).card * s ∧
    (univ.filter (fun i => w i < 1)).card + (univ.filter (fun i => ¬ w i < 1)).card = m := by
  refine ⟨?_, core_sum_ge h hs, ?_⟩
  · have := count_points h hs
    rwa [Fintype.card_fin] at this
  · have := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin m)))
      (fun i => w i < 1)
    rwa [Finset.card_univ, Fintype.card_fin] at this

lemma part_b {s n : ℕ} (hs : 0 < s) (hsn : s ≤ n) (S : Fin (cost s n) → Finset (Fin n))
    (w : Fin (cost s n) → ℝ) (h : GC s S w) :
    let core := (Finset.univ : Finset (Fin (cost s n))).filter (fun i => w i < 1)
    let sites := core.biUnion S
    (∀ i, w i ≤ 1) ∧ (∀ i, w i = 1 ↔ ∀ j, i ≠ j → Disjoint (S i) (S j)) ∧
    (∀ y ∈ sites, 2 ≤ (core.filter (fun i => y ∈ S i)).card) ∧
    sites.card ≤ (s-1)*(s+n % s) ∧ s*core.card ≤ 2*((cost s n)*s-n) := by
  intro core sites
  refine ⟨w_le h hs, iso_iff h hs, fun y hy => deg2 h hs y hy, ?_, ?_⟩
  · obtain ⟨e1, e2, e3⟩ := counts hs h
    have hm := cost_le_gen hs hsn
    rw [← e3] at hm
    have e := Nat.div_add_mod n s
    have hq : 1 ≤ n / s := (Nat.one_le_div_iff hs).mpr hsn
    obtain ⟨q', hq'⟩ : ∃ q', n / s = q' + 1 := ⟨n / s - 1, by omega⟩
    rw [hq'] at e hm
    obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at hm ⊢
    have hm2 := Nat.mul_le_mul_right (t + 1) hm
    change sites.card ≤ _
    generalize sites.card = P at *
    generalize (univ.filter (fun i => w i < 1)).card = c at *
    generalize (univ.filter (fun i => ¬ w i < 1)).card = k at *
    generalize n % (t + 1) = a at *
    nlinarith
  · obtain ⟨e1, e2, e3⟩ := counts hs h
    change s * (univ.filter (fun i => w i < 1)).card ≤ _
    have hms : cost s n * s = (univ.filter (fun i => w i < 1)).card * s +
        (univ.filter (fun i => ¬ w i < 1)).card * s := by rw [← add_mul, e3]
    rw [hms, mul_comm s]
    omega

lemma part_c {s n : ℕ} (hs : 0 < s) (h2 : 2 * s * s ≤ n) : cost s (n + s) = cost s n + 1 := by
  have hsn : s ≤ n := by nlinarith
  apply le_antisymm
  · obtain ⟨S, w, h⟩ := cost_spec hs hsn
    apply cost_le_hc (hc_sum (hc_of_fin h) (hc_blocks s 1))
    simp
  · obtain ⟨S, w, h⟩ := cost_spec hs (by omega : s ≤ n + s)
    obtain ⟨i₀, hi₀⟩ : ∃ i₀, ¬ w i₀ < 1 := by
      by_contra hall
      push Not at hall
      have hb := (part_b hs (by omega) S w h).2.2.2.1
      obtain ⟨e1, -, -⟩ := counts hs h
      have h0 : (univ.filter (fun i => ¬ w i < 1)).card = 0 := by
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro i _; simpa using hall i
      rw [h0, zero_mul, zero_add] at e1
      change ((univ.filter (fun i => w i < 1)).biUnion S).card ≤ _ at hb
      rw [← e1] at hb
      have ha : (n + s) % s < s := Nat.mod_lt _ hs
      obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
      simp only [Nat.add_sub_cancel] at hb
      generalize (n + (t + 1)) % (t + 1) = a at *
      have := Nat.mul_le_mul_left t (show a ≤ t by omega)
      nlinarith
    have hp := hc_peel h hs hi₀
    have := cost_le_hc hp (n := n) (by rw [card_peel h i₀]; omega)
    have : 0 < cost s (n + s) := Fin.pos i₀
    omega

lemma struct_d {h q m N : ℕ} (hh : 0 < h) (hN : N = q * (h + h) + h)
    {S : Fin m → Finset (Fin N)} {w : Fin m → ℝ} (hG : GC (h + h) S w) :
    3 ≤ (univ.filter (fun i => w i < 1)).card ∧
    (univ.filter (fun i => ¬ w i < 1)).card ≤ q ∧
    2 * q + 1 ≤ 2 * (univ.filter (fun i => ¬ w i < 1)).card +
      (univ.filter (fun i => w i < 1)).card := by
  have hs : 0 < h + h := by omega
  obtain ⟨e1, e2, -⟩ := counts hs hG
  have hsum := core_count hG
  set C := univ.filter (fun i => w i < 1) with hC
  set P := (C.biUnion S).card with hPdef
  set k := (univ.filter (fun i => ¬ w i < 1)).card
  have hle : ∑ y ∈ C.biUnion S, (C.filter (fun i => y ∈ S i)).card ≤ P * C.card := by
    rw [hPdef, ← smul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum (fun y _ => Finset.card_filter_le _ _)
  rw [hN] at e1
  have hP : 0 < P := by
    by_contra h0
    have : P = 0 := by omega
    rw [this] at e1
    have : h * (2 * q + 1) = h * (2 * k) := by ring_nf; ring_nf at e1; linarith
    have := Nat.eq_of_mul_eq_mul_left hh this
    omega
  have hc2 : 2 ≤ C.card := by
    obtain ⟨y, hy⟩ : (C.biUnion S).Nonempty := Finset.card_pos.mp hP
    exact (deg2 hG hs y hy).trans (Finset.card_le_card (Finset.filter_subset _ _))
  have hc3 : 3 ≤ C.card := by
    by_contra hc
    have hc' : C.card = 2 := by omega
    rw [hsum, hc'] at hle
    rw [hc'] at e2
    have hP2 : P = h + h := by nlinarith
    rw [hP2] at e1
    have : h * (2 * q + 1) = h * (2 * (k + 1)) := by ring_nf; ring_nf at e1; linarith
    have := Nat.eq_of_mul_eq_mul_left hh this
    omega
  refine ⟨hc3, ?_, ?_⟩
  · have : h * (2 * k) ≤ h * (2 * q + 1) := by nlinarith
    have := Nat.le_of_mul_le_mul_left this hh
    omega
  · have : h * (2 * q + 1) ≤ h * (2 * k + C.card) := by nlinarith
    exact Nat.le_of_mul_le_mul_left this hh

lemma pair_sum {s m N : ℕ} {S : Fin m → Finset (Fin N)} {w : Fin m → ℝ} (hG : GC s S w)
    {a b : Fin m} (hab : a ≠ b) {y : Fin N} (ha : y ∈ S a) (hb : y ∈ S b)
    (ho : ∀ c, c ≠ a → c ≠ b → y ∉ S c) : w a + w b = 1 := by
  rw [← hG.2 y, Finset.sum_eq_add a b hab]
  · simp [ha, hb]
  · intro c _ hc; simp [ho c hc.1 hc.2]
  · simp
  · simp

lemma part_d {s : ℕ} (hs : 0 < s) (q : ℕ) (hq : 0 < q) (he : Even s) :
    let n := q*s+s/2
    cost s n = q+2 ∧
    ∀ (S : Fin (q+2) → Finset (Fin n)) (w : Fin (q+2) → ℝ), GC s S w →
      let core := (Finset.univ : Finset (Fin (q+2))).filter (fun i => w i < 1)
      core.card = 3 ∧ (∀ i ∈ core, 2*w i = 1) ∧
      (∀ i ∈ core, ∀ j ∈ core, i ≠ j → ((S i) ∩ (S j)).card = s/2) ∧
      ∀ y ∈ core.biUnion S, (core.filter (fun i => y ∈ S i)).card = 2 := by
  intro n
  obtain ⟨h, rfl⟩ := he
  have hh : 0 < h := by omega
  have hN : n = q * (h + h) + h := by simp only [n]; omega
  have hhalf : (h + h) / 2 = h := by omega
  rw [hhalf]
  refine ⟨?_, ?_⟩
  · apply le_antisymm
    · have := cost_le_hc (hc_sum (hc_blocks (h + h) (q - 1)) hc_three) (n := n) (by
        rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_prod, Fintype.card_fin,
          Fintype.card_fin, Fintype.card_fin, Fintype.card_fin, hN]
        obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
        simp only [Nat.add_sub_cancel]; ring)
      omega
    · obtain ⟨S, w, hG⟩ := cost_spec (n := n) (by omega : 0 < h + h) (by rw [hN]; nlinarith)
      obtain ⟨h1, h2, h3⟩ := struct_d hh hN hG
      obtain ⟨-, -, e3⟩ := counts (by omega : 0 < h + h) hG
      omega
  · intro S w hG
    dsimp only
    have hs' : 0 < h + h := by omega
    obtain ⟨h1, h2, h3⟩ := struct_d hh hN hG
    obtain ⟨e1, e2, e3⟩ := counts hs' hG
    have hsum := core_count hG
    set C := (univ : Finset (Fin (q+2))).filter (fun i => w i < 1) with hC
    set k := (univ.filter (fun i => ¬ w i < 1)).card with hk
    set P := (C.biUnion S).card with hPdef
    have hc : C.card = 3 := by omega
    have hk1 : k = q - 1 := by omega
    rw [hk1, hN] at e1
    have hP : P = 3 * h := by
      obtain ⟨r, hr⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
      rw [hr, Nat.add_sub_cancel] at e1
      ring_nf at e1; omega
    have hdeg : ∀ y ∈ C.biUnion S, (C.filter (fun i => y ∈ S i)).card = 2 := by
      by_contra hno
      push Not at hno
      obtain ⟨y₀, hy₀, hne⟩ := hno
      have hlt : ∑ _y ∈ C.biUnion S, 2 < ∑ y ∈ C.biUnion S, (C.filter (fun i => y ∈ S i)).card := by
        apply Finset.sum_lt_sum (fun y hy => deg2 hG hs' y hy)
        exact ⟨y₀, hy₀, lt_of_le_of_ne (deg2 hG hs' y₀ hy₀) (Ne.symm hne)⟩
      rw [hsum, Finset.sum_const, smul_eq_mul, hc, ← hPdef, hP] at hlt
      omega
    obtain ⟨i, j, l, hij, hil, hjl, hCeq⟩ := Finset.card_eq_three.mp hc
    have hcnt : ∀ y, (C.filter (fun x => y ∈ S x)).card = (if y ∈ S i then 1 else 0) +
        ((if y ∈ S j then 1 else 0) + (if y ∈ S l then 1 else 0)) := by
      intro y
      rw [hCeq, Finset.card_filter, Finset.sum_insert (by simp [hij, hil]),
        Finset.sum_insert (by simp [hjl]), Finset.sum_singleton]
    have hiC : i ∈ C := by rw [hCeq]; simp
    have hjC : j ∈ C := by rw [hCeq]; simp
    have hlC : l ∈ C := by rw [hCeq]; simp
    have hmemC : ∀ x ∈ C, ∀ y ∈ S x, y ∈ C.biUnion S :=
      fun x hx y hy => Finset.mem_biUnion.mpr ⟨x, hx, hy⟩
    have two : ∀ y, y ∈ S i ∨ y ∈ S j ∨ y ∈ S l → (if y ∈ S i then 1 else 0) +
        ((if y ∈ S j then 1 else 0) + (if y ∈ S l then 1 else 0)) = 2 := by
      intro y hy
      rw [← hcnt]
      rcases hy with hy | hy | hy
      exacts [hdeg y (hmemC i hiC y hy), hdeg y (hmemC j hjC y hy), hdeg y (hmemC l hlC y hy)]
    have ex : ∀ y, (y ∈ S i → ((y ∈ S j ∧ y ∉ S l) ∨ (y ∉ S j ∧ y ∈ S l))) ∧
        (y ∈ S j → ((y ∈ S i ∧ y ∉ S l) ∨ (y ∉ S i ∧ y ∈ S l))) ∧
        (y ∈ S l → ((y ∈ S i ∧ y ∉ S j) ∨ (y ∉ S i ∧ y ∈ S j))) := by
      intro y
      by_cases a : y ∈ S i <;> by_cases b : y ∈ S j <;> by_cases c : y ∈ S l <;>
        first
          | (simp [a, b, c]; done)
          | (have := two y (by tauto); simp [a, b, c] at this)
    have split : ∀ a b c : Fin (q+2),
        (∀ y ∈ S a, (y ∈ S b ∧ y ∉ S c) ∨ (y ∉ S b ∧ y ∈ S c)) →
        (S a).card = (S a ∩ S b).card + (S a ∩ S c).card := by
      intro a b c hab
      rw [← Finset.card_union_of_disjoint]
      · congr 1; ext y; simp only [Finset.mem_union, Finset.mem_inter]; constructor
        · intro hy
          rcases hab y hy with h' | h'
          exacts [Or.inl ⟨hy, h'.1⟩, Or.inr ⟨hy, h'.2⟩]
        · rintro (⟨hy, -⟩ | ⟨hy, -⟩) <;> exact hy
      · rw [Finset.disjoint_left]; intro y hy hy'
        simp only [Finset.mem_inter] at hy hy'
        rcases hab y hy.1 with h' | h'
        · exact h'.2 hy'.2
        · exact h'.1 hy.2
    have ci := split i j l (fun y hy => (ex y).1 hy)
    have cj := split j i l (fun y hy => (ex y).2.1 hy)
    have cl := split l i j (fun y hy => (ex y).2.2 hy)
    rw [(hG.1 _).1] at ci cj cl
    rw [Finset.inter_comm (S j) (S i)] at cj
    rw [Finset.inter_comm (S l) (S i), Finset.inter_comm (S l) (S j)] at cl
    have xij : (S i ∩ S j).card = h := by omega
    have xil : (S i ∩ S l).card = h := by omega
    have xjl : (S j ∩ S l).card = h := by omega
    have oth : ∀ (y : Fin n) (a b d : Fin (q+2)), C = {a, b, d} → y ∈ S a → y ∉ S d →
        ∀ c, c ≠ a → c ≠ b → y ∉ S c := by
      intro y a b d hC' ha hd c hca hcb hc'
      by_cases hw : w c < 1
      · have : c ∈ C := by rw [hC]; simp [hw]
        rw [hC'] at this
        simp only [Finset.mem_insert, Finset.mem_singleton] at this
        rcases this with h' | h' | h'
        · exact hca h'
        · exact hcb h'
        · exact hd (h' ▸ hc')
      · exact Finset.disjoint_left.mp (noncore_iso hG hs' hw a hca) hc' ha
    have pick : ∀ a b : Fin (q+2), 0 < (S a ∩ S b).card → ∃ y, y ∈ S a ∧ y ∈ S b := by
      intro a b hp
      obtain ⟨y, hy⟩ := Finset.card_pos.mp hp
      exact ⟨y, (Finset.mem_inter.mp hy).1, (Finset.mem_inter.mp hy).2⟩
    have wij : w i + w j = 1 := by
      obtain ⟨y, ha, hb⟩ := pick i j (by omega)
      have hd : y ∉ S l := by rcases (ex y).1 ha with h' | h'; exacts [h'.2, absurd hb h'.1]
      exact pair_sum hG hij ha hb (oth y i j l hCeq ha hd)
    have wil : w i + w l = 1 := by
      obtain ⟨y, ha, hb⟩ := pick i l (by omega)
      have hd : y ∉ S j := by rcases (ex y).1 ha with h' | h'; exacts [absurd hb h'.2, h'.1]
      exact pair_sum hG hil ha hb (oth y i l j (by rw [hCeq]; ext; simp; tauto) ha hd)
    have wjl : w j + w l = 1 := by
      obtain ⟨y, ha, hb⟩ := pick j l (by omega)
      have hd : y ∉ S i := by rcases (ex y).2.1 ha with h' | h'; exacts [absurd hb h'.2, h'.1]
      exact pair_sum hG hjl ha hb (oth y j l i (by rw [hCeq]; ext; simp; tauto) ha hd)
    refine ⟨hc, ?_, ?_, hdeg⟩
    · intro x hx
      rw [hCeq] at hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> linarith
    · intro a ha b hb hab
      rw [hCeq] at ha hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
      rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
        first
          | exact absurd rfl hab
          | assumption
          | rwa [Finset.inter_comm]

end PEqualNP.Outside.L_lib_1027_aux

open PEqualNP.Outside.L_lib_1027_aux in
theorem PEqualNP.Outside.L_lib_1027 : (∀ s : ℕ, 0 < s →
  let cover := fun (n m : ℕ) (S : Fin m → Finset (Fin n)) (w : Fin m → ℝ) =>
    (∀ i, (S i).card = s ∧ 0 < w i) ∧ ∀ y, (∑ i, if y ∈ S i then w i else 0) = 1
  let cost := fun n : ℕ => sInf {m : ℕ | ∃ S w, cover n m S w}
  (∀ n : ℕ, s ≤ n →
    (∃ S w, cover n (cost n) S w) ∧
    (∀ (S : Fin (cost n) → Finset (Fin n)) (w : Fin (cost n) → ℝ),
      cover n (cost n) S w →
      let core := (Finset.univ : Finset (Fin (cost n))).filter (fun i => w i < 1)
      let sites := core.biUnion S
      (∀ i, w i ≤ 1) ∧ (∀ i, w i = 1 ↔ ∀ j, i ≠ j → Disjoint (S i) (S j)) ∧
      (∀ y ∈ sites, 2 ≤ (core.filter (fun i => y ∈ S i)).card) ∧
      sites.card ≤ (s-1)*(s+n % s) ∧ s*core.card ≤ 2*((cost n)*s-n)) ∧
    (2*s*s ≤ n → cost (n+s) = cost n + 1)) ∧
  ∀ q : ℕ, 0 < q → Even s →
    let n := q*s+s/2
    cost n = q+2 ∧
    ∀ (S : Fin (q+2) → Finset (Fin n)) (w : Fin (q+2) → ℝ), cover n (q+2) S w →
      let core := (Finset.univ : Finset (Fin (q+2))).filter (fun i => w i < 1)
      core.card = 3 ∧ (∀ i ∈ core, 2*w i = 1) ∧
      (∀ i ∈ core, ∀ j ∈ core, i ≠ j → ((S i) ∩ (S j)).card = s/2) ∧
      ∀ y ∈ core.biUnion S, (core.filter (fun i => y ∈ S i)).card = 2) := by
  intro s hs cover cost
  exact ⟨fun n hsn => ⟨cost_spec hs hsn, fun S w hG => part_b hs hsn S w hG,
    fun h2 => part_c hs h2⟩, fun q hq he => part_d hs q hq he⟩
