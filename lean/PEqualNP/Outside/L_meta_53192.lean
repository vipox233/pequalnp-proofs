import PEqualNP.Defs
import Mathlib.Combinatorics.SimpleGraph.Tutte
import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace PEqualNP.Outside.L_meta_53192

open Finset

abbrev Sets (t j : ℕ) := {S : Finset (Fin t) // S.card = j}

lemma card_sets (t j : ℕ) : Fintype.card (Sets t j) = t.choose j := by
  simp [Sets]

/-- Hall: cada j-conjunto recibe un (t-1-j)-conjunto disjunto distinto. -/
lemma layer (t j : ℕ) (hj : 2 * j + 1 < t) :
    ∃ h : Sets t j → Sets t (t - 1 - j), Function.Injective h ∧ ∀ a, Disjoint a.1 (h a).1 := by
  classical
  have key := (Fintype.all_card_le_filter_rel_iff_exists_injective
    (fun (a : Sets t j) (b : Sets t (t - 1 - j)) => Disjoint a.1 b.1)).1
  apply key
  intro A
  set N := univ.filter (fun b : Sets t (t - 1 - j) => ∃ a ∈ A, Disjoint a.1 b.1) with hN
  set d1 := (t - j).choose (t - 1 - j) with hd1
  set d2 := (t - (t - 1 - j)).choose j with hd2
  have left : ∀ a ∈ A, d1 ≤ (N.filter (fun b => Disjoint a.1 b.1)).card := by
    intro a ha
    have : (powersetCard (t - 1 - j) (a.1ᶜ)).card ≤ ((N.filter (fun b => Disjoint a.1 b.1)).image (fun b => b.1)).card := by
      apply card_le_card
      intro B hB
      obtain ⟨hsub, hc⟩ := mem_powersetCard.1 hB
      have dis : Disjoint a.1 B := disjoint_of_subset_right hsub disjoint_compl_right
      refine mem_image.2 ⟨⟨B, hc⟩, mem_filter.2 ⟨mem_filter.2 ⟨mem_univ _, a, ha, dis⟩, dis⟩, rfl⟩
    rw [card_powersetCard, card_compl, Fintype.card_fin, a.2] at this
    exact this.trans card_image_le
  have right : ∀ b ∈ N, (A.filter (fun a => Disjoint a.1 b.1)).card ≤ d2 := by
    intro b _
    have : ((A.filter (fun a => Disjoint a.1 b.1)).image (fun a => a.1)).card ≤ (powersetCard j (b.1ᶜ)).card := by
      apply card_le_card
      intro S hS
      obtain ⟨a, ha, rfl⟩ := mem_image.1 hS
      exact mem_powersetCard.2 ⟨(mem_filter.1 ha).2.le_compl_right, a.2⟩
    rw [card_powersetCard, card_compl, Fintype.card_fin, b.2,
      card_image_of_injective _ Subtype.val_injective] at this
    exact this
  have count : A.card * d1 ≤ N.card * d2 := by
    apply Finset.card_mul_le_card_mul (fun (a : Sets t j) (b : Sets t (t - 1 - j)) => Disjoint a.1 b.1)
    · intro a ha; exact left a ha
    · intro b hb; exact right b hb
  have e1 : d1 = t - j := by
    rw [hd1]
    have : t - j = (t - 1 - j) + 1 := by omega
    rw [this, Nat.choose_succ_self_right]
  have e2 : d2 = j + 1 := by
    rw [hd2]
    have : t - (t - 1 - j) = j + 1 := by omega
    rw [this, Nat.choose_succ_self_right]
  rw [e1, e2] at count
  have le : j + 1 ≤ t - j := by omega
  have : A.card * (j + 1) ≤ N.card * (j + 1) := le_trans (Nat.mul_le_mul_left _ le) count
  exact Nat.le_of_mul_le_mul_right this (Nat.succ_pos _)

section Cut
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Numero de aristas que salen de T. -/
def cut (T : Finset V) : ℕ := ∑ u, ∑ v, if G.Adj u v ∧ u ∈ T ∧ v ∉ T then 1 else 0

lemma two_cut (T : Finset V) : 2 * cut G T =
    ∑ u, ∑ v, ((if G.Adj u v ∧ u ∈ T ∧ v ∉ T then 1 else 0) + (if G.Adj v u ∧ v ∈ T ∧ u ∉ T then 1 else 0)) := by
  simp only [sum_add_distrib]
  rw [two_mul]
  congr 1
  unfold cut
  rw [sum_comm]

lemma posimodular (A B : Finset V) : cut G (A \ B) + cut G (B \ A) ≤ cut G A + cut G B := by
  have : 2 * cut G (A \ B) + 2 * cut G (B \ A) ≤ 2 * cut G A + 2 * cut G B := by
    rw [two_cut, two_cut, two_cut, two_cut]
    simp only [← sum_add_distrib]
    refine sum_le_sum (fun u _ => sum_le_sum (fun v _ => ?_))
    by_cases h : G.Adj u v
    · have h' := h.symm
      by_cases a : u ∈ A <;> by_cases b : u ∈ B <;> by_cases c : v ∈ A <;> by_cases e : v ∈ B <;>
        simp [h, h', a, b, c, e]
    · have h' : ¬ G.Adj v u := fun x => h x.symm
      simp [h, h']
  omega

variable (d : ℕ) (reg : ∀ v, (univ.filter (fun w => G.Adj v w)).card = d)
  (trans : ∀ a b : V, ∃ g : V ≃ V, g a = b ∧ ∀ x y, G.Adj (g x) (g y) ↔ G.Adj x y)
  (conn : ∀ T : Finset V, T.Nonempty → (∀ u ∈ T, ∀ v, G.Adj u v → v ∈ T) → T = univ)

lemma cut_map (g : V ≃ V) (hg : ∀ x y, G.Adj (g x) (g y) ↔ G.Adj x y) (T : Finset V) :
    cut G (T.map g.toEmbedding) = cut G T := by
  unfold cut
  rw [← Equiv.sum_comp g]
  refine sum_congr rfl (fun u _ => ?_)
  rw [← Equiv.sum_comp g]
  refine sum_congr rfl (fun v _ => ?_)
  simp [hg]

include reg trans conn in
lemma cut_ge (T : Finset V) (ne : T.Nonempty) (proper : T ≠ univ) : d ≤ cut G T := by
  classical
  by_contra hlt
  let Bad : Finset V → Prop := fun S => S.Nonempty ∧ S ≠ univ ∧ cut G S < d
  have ex : ((univ : Finset (Finset V)).filter Bad).Nonempty :=
    ⟨T, mem_filter.2 ⟨mem_univ _, ne, proper, not_le.1 hlt⟩⟩
  obtain ⟨A, hA, hmin⟩ := exists_min_image _ card ex
  obtain ⟨-, Ane, Apr, Acut⟩ := mem_filter.1 hA
  have atom : ∀ g : V ≃ V, (∀ x y, G.Adj (g x) (g y) ↔ G.Adj x y) →
      (∃ a ∈ A, g a ∈ A) → A.map g.toEmbedding = A := by
    intro g hg ⟨a, ha, hga⟩
    set B := A.map g.toEmbedding with hB
    have cardB : B.card = A.card := card_map _
    by_contra hne
    have meet : g a ∈ A ∩ B := mem_inter.2 ⟨hga, mem_map.2 ⟨a, ha, rfl⟩⟩
    have ne1 : (A \ B).Nonempty := by
      rw [sdiff_nonempty]
      intro sub
      exact hne (eq_of_subset_of_card_le sub (by omega)).symm
    have ne2 : (B \ A).Nonempty := by
      rw [sdiff_nonempty]
      intro sub
      exact hne (eq_of_subset_of_card_le sub (by omega))
    have small : ∀ S T' : Finset V, S.card = A.card → (∃ x, x ∈ S ∧ x ∈ T') → (S \ T').Nonempty → d ≤ cut G (S \ T') := by
      intro S T' hS ⟨x, hx1, hx2⟩ hne'
      by_contra h
      have lt : (S \ T').card < A.card := by
        rw [← hS]
        refine card_lt_card ⟨sdiff_subset, fun sub => ?_⟩
        exact (mem_sdiff.1 (sub hx1)).2 hx2
      have bad : S \ T' ∈ (univ : Finset (Finset V)).filter Bad := by
        refine mem_filter.2 ⟨mem_univ _, hne', fun e => ?_, not_le.1 h⟩
        have : x ∈ S \ T' := e ▸ mem_univ x
        exact (mem_sdiff.1 this).2 hx2
      exact absurd (hmin _ bad) (not_le.2 lt)
    have c1 := small A B rfl ⟨g a, (mem_inter.1 meet).1, (mem_inter.1 meet).2⟩ ne1
    have c2 := small B A cardB ⟨g a, (mem_inter.1 meet).2, (mem_inter.1 meet).1⟩ ne2
    have p := posimodular G A B
    have : cut G B = cut G A := cut_map G g hg A
    omega
  obtain ⟨a0, ha0⟩ := Ane
  set r := (A.filter (fun w => G.Adj a0 w)).card with hr
  have inner : ∀ a ∈ A, (A.filter (fun w => G.Adj a w)).card = r := by
    intro a ha
    obtain ⟨g, hg, hadj⟩ := trans a0 a
    have fix := atom g hadj ⟨a0, ha0, hg ▸ ha⟩
    have : A.filter (fun w => G.Adj a w) = (A.filter (fun w => G.Adj a0 w)).map g.toEmbedding := by
      ext w
      simp only [mem_filter, mem_map, Equiv.coe_toEmbedding]
      constructor
      · rintro ⟨hw, hadj'⟩
        rw [← fix] at hw
        obtain ⟨x, hx, rfl⟩ := mem_map.1 hw
        refine ⟨x, ⟨hx, ?_⟩, rfl⟩
        rw [← hadj, hg]
        exact hadj'
      · rintro ⟨x, ⟨hx, h⟩, rfl⟩
        refine ⟨?_, ?_⟩
        · rw [← fix]; exact mem_map.2 ⟨x, hx, rfl⟩
        · rw [← hg]; exact (hadj _ _).2 h
    rw [this, card_map]
  have outer : ∀ a ∈ A, (univ.filter (fun w => G.Adj a w ∧ w ∉ A)).card = d - r := by
    intro a ha
    have split := card_filter_add_card_filter_not (s := univ.filter (fun w => G.Adj a w)) (fun w => w ∈ A)
    have e1 : (univ.filter (fun w => G.Adj a w)).filter (fun w => w ∈ A) = A.filter (fun w => G.Adj a w) := by
      ext w; simp [and_comm]
    have e2 : (univ.filter (fun w => G.Adj a w)).filter (fun w => w ∉ A) = univ.filter (fun w => G.Adj a w ∧ w ∉ A) := by
      rw [filter_filter]
    rw [e1, e2, inner a ha, reg a] at split
    omega
  have value : cut G A = A.card * (d - r) := by
    unfold cut
    rw [← sum_subset (subset_univ A) (fun u _ hu => by simp [hu])]
    rw [← smul_eq_mul, ← sum_const]
    refine sum_congr rfl (fun u hu => ?_)
    rw [← outer u hu, card_filter]
    refine sum_congr rfl (fun v _ => ?_)
    simp [hu]
  have rd : r ≤ d := by
    rw [← reg a0]
    exact card_le_card (fun w hw => mem_filter.2 ⟨mem_univ _, (mem_filter.1 hw).2⟩)
  have rA : r < A.card := by
    refine card_lt_card ⟨filter_subset _ _, fun sub => ?_⟩
    exact G.irrefl (mem_filter.1 (sub ha0)).2
  have rne : r ≠ d := by
    intro e
    have zero : cut G A = 0 := by rw [value, e, Nat.sub_self, Nat.mul_zero]
    have closed : ∀ u ∈ A, ∀ v, G.Adj u v → v ∈ A := by
      intro u hu v huv
      by_contra hv
      have : v ∈ univ.filter (fun w => G.Adj u w ∧ w ∉ A) := mem_filter.2 ⟨mem_univ _, huv, hv⟩
      have c := outer u hu
      rw [e, Nat.sub_self, card_eq_zero] at c
      rw [c] at this
      exact notMem_empty _ this
    exact Apr (conn A ⟨a0, ha0⟩ closed)
  have : d ≤ (r + 1) * (d - r) := by
    obtain ⟨s, hs⟩ : ∃ s, d = r + 1 + s := ⟨d - r - 1, by omega⟩
    have e : d - r = s + 1 := by omega
    rw [e, hs]
    nlinarith
  have : d ≤ cut G A := by
    rw [value]
    exact this.trans (Nat.mul_le_mul_right _ (by omega))
  omega

include reg trans conn in
/-- Tutte: al quitar S (conteniendo lo borrado) los componentes impares no superan |S|. -/
lemma odd_le (hd : 0 < d) (S : Finset V) (Sne : S.Nonempty) (W : Finset (Finset V))
    (disj : ∀ C ∈ W, ∀ C' ∈ W, C ≠ C' → Disjoint C C') (ne : ∀ C ∈ W, C.Nonempty)
    (out : ∀ C ∈ W, Disjoint C S) (closed : ∀ C ∈ W, ∀ u ∈ C, ∀ v, G.Adj u v → v ∈ C ∨ v ∈ S) :
    W.card ≤ S.card := by
  have each : ∀ C ∈ W, d ≤ cut G C := by
    intro C hC
    refine cut_ge G d reg trans conn C (ne C hC) (fun e => ?_)
    obtain ⟨s, hs⟩ := Sne
    exact disjoint_left.1 (out C hC) (e ▸ mem_univ s) hs
  have bound : ∑ C ∈ W, cut G C ≤ S.card * d := by
    have step : ∀ C ∈ W, cut G C ≤ ∑ v ∈ S, ∑ u, if G.Adj u v ∧ u ∈ C then 1 else 0 := by
      intro C hC
      unfold cut
      rw [sum_comm (s := S)]
      refine sum_le_sum (fun u _ => ?_)
      rw [← sum_subset (subset_univ S) (f := fun v => if G.Adj u v ∧ u ∈ C ∧ v ∉ C then 1 else 0)]
      · refine sum_le_sum (fun v _ => ?_)
        by_cases h : G.Adj u v ∧ u ∈ C ∧ v ∉ C
        · rw [if_pos h, if_pos ⟨h.1, h.2.1⟩]
        · rw [if_neg h]; exact Nat.zero_le _
      · intro v _ hv
        rw [if_neg]
        rintro ⟨h1, h2, h3⟩
        rcases closed C hC u h2 v h1 with h | h
        · exact h3 h
        · exact hv h
    refine (sum_le_sum step).trans ?_
    rw [sum_comm, ← smul_eq_mul, ← sum_const]
    refine sum_le_sum (fun v _ => ?_)
    rw [sum_comm]
    have : ∀ u, (∑ C ∈ W, if G.Adj u v ∧ u ∈ C then 1 else 0) ≤ if G.Adj v u then 1 else 0 := by
      intro u
      by_cases h : G.Adj u v
      · rw [if_pos h.symm]
        rw [← card_filter]
        refine card_le_one.2 (fun C hC C' hC' => ?_)
        obtain ⟨c1, -, c2⟩ := mem_filter.1 hC
        obtain ⟨c3, -, c4⟩ := mem_filter.1 hC'
        by_contra hne
        exact disjoint_left.1 (disj C c1 C' c3 hne) c2 c4
      · have : ∀ C ∈ W, (if G.Adj u v ∧ u ∈ C then 1 else 0) = 0 := fun C _ => if_neg (fun x => h x.1)
        rw [sum_eq_zero this]
        exact Nat.zero_le _
    refine (sum_le_sum (fun u _ => this u)).trans ?_
    rw [← card_filter, reg v]
  have low : W.card * d ≤ ∑ C ∈ W, cut G C := by
    rw [← smul_eq_mul, ← sum_const]
    exact sum_le_sum each
  exact Nat.le_of_mul_le_mul_right (low.trans bound) hd

end Cut

section Odd
variable (k : ℕ)

def odd : SimpleGraph (Sets (2 * k + 1) k) where
  Adj a b := a ≠ b ∧ Disjoint a.1 b.1
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

lemma odd_adj (hk : 0 < k) (a b : Sets (2 * k + 1) k) : (odd k).Adj a b ↔ Disjoint a.1 b.1 := by
  refine ⟨fun h => h.2, fun h => ⟨fun e => ?_, h⟩⟩
  subst e
  have : a.1 = ∅ := by simpa using disjoint_self.1 h
  have := a.2
  simp_all

instance : DecidableRel (odd k).Adj := fun a b => by unfold odd; infer_instance

lemma odd_reg (hk : 0 < k) (a : Sets (2 * k + 1) k) : (univ.filter (fun w => (odd k).Adj a w)).card = k + 1 := by
  have e : (univ.filter (fun w => (odd k).Adj a w)).image (fun w => w.1) = powersetCard k (a.1ᶜ) := by
    ext B
    simp only [mem_image, mem_filter, mem_univ, true_and, mem_powersetCard]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨((odd_adj k hk _ _).1 hw).le_compl_left, w.2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨B, h2⟩, (odd_adj k hk _ _).2 (disjoint_of_subset_right h1 disjoint_compl_right), rfl⟩
  have := congrArg card e
  rw [card_image_of_injective _ Subtype.val_injective, card_powersetCard, card_compl, Fintype.card_fin, a.2] at this
  rw [this]
  have : 2 * k + 1 - k = k + 1 := by omega
  rw [this, Nat.choose_succ_self_right]

lemma odd_trans (hk : 0 < k) (a b : Sets (2 * k + 1) k) :
    ∃ g : Sets (2 * k + 1) k ≃ Sets (2 * k + 1) k, g a = b ∧ ∀ x y, (odd k).Adj (g x) (g y) ↔ (odd k).Adj x y := by
  classical
  have e : {i // i ∈ a.1} ≃ {i // i ∈ b.1} := Finset.equivOfCardEq (a.2.trans b.2.symm)
  let σ : Equiv.Perm (Fin (2 * k + 1)) := e.extendSubtype
  have hσ : a.1.map σ.toEmbedding = b.1 := by
    refine eq_of_subset_of_card_le (fun x hx => ?_) (by rw [card_map, a.2, b.2])
    obtain ⟨y, hy, rfl⟩ := mem_map.1 hx
    exact e.extendSubtype_mem y hy
  let g : Sets (2 * k + 1) k ≃ Sets (2 * k + 1) k :=
    { toFun := fun x => ⟨x.1.map σ.toEmbedding, by rw [card_map, x.2]⟩
      invFun := fun x => ⟨x.1.map σ.symm.toEmbedding, by rw [card_map, x.2]⟩
      left_inv := fun x => Subtype.ext (by ext i; simp [mem_map_equiv])
      right_inv := fun x => Subtype.ext (by ext i; simp [mem_map_equiv]) }
  refine ⟨g, Subtype.ext hσ, fun x y => ?_⟩
  rw [odd_adj k hk, odd_adj k hk]
  exact disjoint_map _

lemma odd_conn (hk : 0 < k) (T : Finset (Sets (2 * k + 1) k)) (ne : T.Nonempty)
    (closed : ∀ u ∈ T, ∀ v, (odd k).Adj u v → v ∈ T) : T = univ := by
  classical
  have swap : ∀ S ∈ T, ∀ S' : Sets (2 * k + 1) k, ∀ x ∈ S.1, ∀ y ∉ S.1, S'.1 = insert y (S.1.erase x) → S' ∈ T := by
    intro S hS S' x hx y hy e
    have ycompl : y ∈ S.1ᶜ := mem_compl.2 hy
    have cardU : (S.1ᶜ.erase y).card = k := by
      rw [card_erase_of_mem ycompl, card_compl, Fintype.card_fin, S.2]
      omega
    let U : Sets (2 * k + 1) k := ⟨S.1ᶜ.erase y, cardU⟩
    have h1 : U ∈ T := closed S hS U ((odd_adj k hk _ _).2
      (disjoint_of_subset_right (erase_subset _ _) disjoint_compl_right))
    refine closed U h1 S' ((odd_adj k hk _ _).2 ?_)
    rw [disjoint_left]
    intro z hz hz'
    obtain ⟨zy, zS⟩ := mem_erase.1 hz
    rw [e] at hz'
    rcases mem_insert.1 hz' with h | h
    · exact zy h
    · exact mem_compl.1 zS (mem_erase.1 h).2
  have reach : ∀ n, ∀ S ∈ T, ∀ S' : Sets (2 * k + 1) k, (S'.1 \ S.1).card = n → S' ∈ T := by
    intro n
    induction n with
    | zero =>
      intro S hS S' h
      rw [card_eq_zero, sdiff_eq_empty_iff_subset] at h
      have : S' = S := Subtype.ext (eq_of_subset_of_card_le h (by rw [S.2, S'.2]))
      rwa [this]
    | succ n ih =>
      intro S hS S' h
      have ne1 : (S'.1 \ S.1).Nonempty := card_pos.1 (by omega)
      obtain ⟨y, hy⟩ := ne1
      obtain ⟨hy1, hy2⟩ := mem_sdiff.1 hy
      have ne2 : (S.1 \ S'.1).Nonempty := by
        rw [sdiff_nonempty]
        intro sub
        have : S.1 = S'.1 := eq_of_subset_of_card_le sub (by rw [S.2, S'.2])
        exact hy2 (this ▸ hy1)
      obtain ⟨x, hx⟩ := ne2
      obtain ⟨hx1, hx2⟩ := mem_sdiff.1 hx
      have cardM : (insert y (S.1.erase x)).card = k := by
        rw [card_insert_of_notMem (fun h => hy2 (mem_erase.1 h).2), card_erase_of_mem hx1, S.2]
        omega
      let M : Sets (2 * k + 1) k := ⟨_, cardM⟩
      have hM : M ∈ T := swap S hS M x hx1 y hy2 rfl
      refine ih M hM S' ?_
      have e : S'.1 \ M.1 = (S'.1 \ S.1).erase y := by
        ext z
        simp only [M, mem_sdiff, mem_insert, mem_erase, not_or, not_and]
        constructor
        · rintro ⟨z1, z2, z3⟩
          refine ⟨z2, z1, fun zS => ?_⟩
          have : z ≠ x := fun e => hx2 (e ▸ z1)
          exact z3 this zS
        · rintro ⟨z2, z1, zS⟩
          exact ⟨z1, z2, fun _ h => zS h⟩
      rw [e, card_erase_of_mem hy, h]
      omega
  obtain ⟨S, hS⟩ := ne
  exact eq_univ_of_forall (fun S' => reach _ S hS S' rfl)

/-- Emparejamiento: floor(C/2) parejas disjuntas de k-conjuntos con t = 2k+1, sin repetir conjuntos. -/
lemma middle (hk : 0 < k) : ∃ (n : ℕ) (a b : Fin n → Sets (2 * k + 1) k),
    n = (2 * k + 1).choose k / 2 ∧ Function.Injective a ∧ Function.Injective b ∧ (∀ i j, a i ≠ b j) ∧
    ∀ i, Disjoint (a i).1 (b i).1 := by
  classical
  have pick : ∀ R : Finset (Sets (2 * k + 1) k), Even (Fintype.card (Sets (2 * k + 1) k) - R.card) →
      (R = ∅ ∨ ∃ v, R = {v}) → ∃ M : (SimpleGraph.induce ((R : Set (Sets (2 * k + 1) k))ᶜ) (odd k)).Subgraph, M.IsPerfectMatching := by
    intro R hev hR
    rw [SimpleGraph.tutte]
    intro u hu
    unfold SimpleGraph.IsTutteViolator at hu
    set H := SimpleGraph.induce ((R : Set (Sets (2 * k + 1) k))ᶜ) (odd k) with hH
    set K := ((⊤ : H.Subgraph).deleteVerts u).coe with hK
    let S : Finset (Sets (2 * k + 1) k) := R ∪ u.toFinset.image Subtype.val
    let supp : K.ConnectedComponent → Finset (Sets (2 * k + 1) k) := fun c =>
      c.supp.toFinset.image (fun x => x.1.1)
    have inj : Function.Injective (fun x : ((⊤ : H.Subgraph).deleteVerts u).verts => x.1.1) :=
      fun x y h => Subtype.ext (Subtype.ext h)
    have mem_supp : ∀ c w, w ∈ supp c ↔ ∃ x ∈ c.supp, x.1.1 = w := by
      intro c w
      simp [supp]
    have notS : ∀ x : ((⊤ : H.Subgraph).deleteVerts u).verts, x.1.1 ∉ S := by
      intro x hx
      rcases mem_union.1 hx with h | h
      · exact x.1.2 h
      · obtain ⟨y, hy, e⟩ := mem_image.1 h
        have : y = x.1 := Subtype.ext e
        have hxu : x.1 ∉ u := x.2.2
        exact hxu (this ▸ Set.mem_toFinset.1 hy)
    have cardSupp : ∀ c, (supp c).card = c.supp.ncard := by
      intro c
      rw [card_image_of_injective _ inj, Set.ncard_eq_toFinset_card']
    have compDisj : ∀ c c', c ≠ c' → Disjoint (supp c) (supp c') := by
      intro c c' hne
      rw [disjoint_left]
      intro w h1 h2
      obtain ⟨x, hx, e1⟩ := (mem_supp _ _).1 h1
      obtain ⟨y, hy, e2⟩ := (mem_supp _ _).1 h2
      have : x = y := inj (e1.trans e2.symm)
      subst this
      exact hne (hx.symm.trans hy)
    have compNe : ∀ c, (supp c).Nonempty := by
      intro c
      obtain ⟨x, hx⟩ := c.nonempty_supp
      exact ⟨x.1.1, (mem_supp _ _).2 ⟨x, hx, rfl⟩⟩
    have compClosed : ∀ c, ∀ w ∈ supp c, ∀ v, (odd k).Adj w v → v ∈ supp c ∨ v ∈ S := by
      intro c w hw v hwv
      obtain ⟨x, hx, rfl⟩ := (mem_supp _ _).1 hw
      by_cases hv : v ∈ S
      · exact Or.inr hv
      · left
        have hvR : v ∉ R := fun h => hv (mem_union_left _ h)
        let v1 : ((R : Set (Sets (2 * k + 1) k))ᶜ : Set _) := ⟨v, hvR⟩
        have hvu : v1 ∉ u := fun h => hv (mem_union_right _ (mem_image.2 ⟨v1, Set.mem_toFinset.2 h, rfl⟩))
        have hv2 : v1 ∈ ((⊤ : H.Subgraph).deleteVerts u).verts := ⟨trivial, hvu⟩
        have adj : K.Adj x ⟨v1, hv2⟩ := by
          have h1 : H.Adj x.1 v1 := hwv
          refine ⟨⟨trivial, x.2.2⟩, ⟨trivial, hvu⟩, h1⟩
        refine (mem_supp _ _).2 ⟨⟨v1, hv2⟩, ?_, rfl⟩
        exact c.mem_supp_of_adj_mem_supp hx adj
    let W : Finset (Finset (Sets (2 * k + 1) k)) := K.oddComponents.toFinset.image supp
    have Wcard : W.card = K.oddComponents.ncard := by
      rw [card_image_of_injOn, Set.ncard_eq_toFinset_card']
      intro c _ c' _ e
      by_contra hne
      have := compDisj c c' hne
      rw [e, disjoint_self] at this
      exact (compNe c').ne_empty this
    by_cases hS : S.Nonempty
    · have le := odd_le (odd k) (k + 1) (odd_reg k hk) (odd_trans k hk) (odd_conn k hk) (Nat.succ_pos _) S hS W
        (by
          intro C hC C' hC' hne
          obtain ⟨c, -, rfl⟩ := mem_image.1 hC
          obtain ⟨c', -, rfl⟩ := mem_image.1 hC'
          exact compDisj c c' (fun e => hne (e ▸ rfl)))
        (by
          intro C hC
          obtain ⟨c, -, rfl⟩ := mem_image.1 hC
          exact compNe c)
        (by
          intro C hC
          obtain ⟨c, -, rfl⟩ := mem_image.1 hC
          rw [disjoint_left]
          intro w hw
          obtain ⟨x, -, rfl⟩ := (mem_supp _ _).1 hw
          exact notS x)
        (by
          intro C hC
          obtain ⟨c, -, rfl⟩ := mem_image.1 hC
          exact compClosed c)
      have uS : S.card ≤ R.card + u.ncard := by
        refine (card_union_le _ _).trans (Nat.add_le_add_left (card_image_le.trans ?_) _)
        rw [Set.ncard_eq_toFinset_card']
      rcases hR with rfl | ⟨v, rfl⟩
      · rw [card_empty] at uS; omega
      · rw [card_singleton] at uS
        have parity : Even (K.oddComponents.ncard + u.ncard) := by
          have h1 : Odd (Nat.card ((⊤ : H.Subgraph).deleteVerts u).verts) ↔ Odd K.oddComponents.ncard :=
            (K.odd_ncard_oddComponents).symm
          have total : Nat.card ((⊤ : H.Subgraph).deleteVerts u).verts + u.ncard =
              Fintype.card (Sets (2 * k + 1) k) - 1 := by
            have e1 : ((⊤ : H.Subgraph).deleteVerts u).verts = uᶜ := by
              ext x; simp
            rw [e1, Nat.card_coe_set_eq, add_comm, Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card]
            have c : ∀ [DecidablePred (fun x : Sets (2 * k + 1) k => x ∈ (({v} : Finset _) : Set (Sets (2 * k + 1) k))ᶜ)],
                (univ.filter (fun x : Sets (2 * k + 1) k => x ∈ (({v} : Finset _) : Set (Sets (2 * k + 1) k))ᶜ)) = univ \ {v} := by
              intro _; ext x; simp
            rw [Fintype.card_subtype, c, card_sdiff_of_subset (subset_univ _), card_univ, card_singleton]
          rw [card_singleton, ← total] at hev
          rw [Nat.even_add] at hev ⊢
          rw [← Nat.not_odd_iff_even, ← Nat.not_odd_iff_even, ← h1, Nat.not_odd_iff_even, Nat.not_odd_iff_even]
          exact hev
        obtain ⟨z, hz⟩ := parity
        omega
    · have S0 : S = ∅ := not_nonempty_iff_eq_empty.1 hS
      have R0 : R = ∅ := by
        rw [← subset_empty, ← S0]; exact subset_union_left
      rw [R0, card_empty, Nat.sub_zero] at hev
      have pos : 0 < K.oddComponents.ncard := by omega
      obtain ⟨c, hc⟩ := (Set.ncard_pos (Set.toFinite _)).1 pos
      have full : supp c = univ := by
        refine odd_conn k hk _ (compNe c) (fun w hw v hv => ?_)
        rcases compClosed c w hw v hv with h | h
        · exact h
        · rw [S0] at h; exact absurd h (notMem_empty _)
      have o : Odd c.supp.ncard := hc
      rw [← cardSupp, full, card_univ] at o
      exact (Nat.not_odd_iff_even.2 hev) o
  have build : ∀ R : Finset (Sets (2 * k + 1) k), Even (Fintype.card (Sets (2 * k + 1) k) - R.card) →
      (R = ∅ ∨ ∃ v, R = {v}) → R.card = Fintype.card (Sets (2 * k + 1) k) % 2 →
      ∃ (n : ℕ) (a b : Fin n → Sets (2 * k + 1) k),
        n = (2 * k + 1).choose k / 2 ∧ Function.Injective a ∧ Function.Injective b ∧ (∀ i j, a i ≠ b j) ∧
        ∀ i, Disjoint (a i).1 (b i).1 := by
    intro R hev hR hc
    obtain ⟨M, hM⟩ := pick R hev hR
    let V' : Set (Sets (2 * k + 1) k) := (R : Set (Sets (2 * k + 1) k))ᶜ
    have ex : ∀ x : V', ∃! y, M.Adj x y := fun x => hM.1 (hM.2 x)
    choose p hp uniq using ex
    have inv : ∀ x, p (p x) = x := fun x => (uniq (p x) x (hp x).symm).symm
    have nofix : ∀ x, p x ≠ x := fun x e => (M.adj_sub (hp x)).ne e.symm
    let ord : V' ≃ Fin (Fintype.card V') := Fintype.equivFin V'
    let E := univ.filter (fun x : V' => ord x < ord (p x))
    have half : 2 * E.card = Fintype.card V' := by
      have img : univ.filter (fun x : V' => ¬ ord x < ord (p x)) = E.image p := by
        ext x
        simp only [E, mem_filter, mem_univ, true_and, mem_image]
        constructor
        · intro h
          refine ⟨p x, ?_, inv x⟩
          rw [inv]
          exact lt_of_le_of_ne (not_lt.1 h) (fun e => nofix x (ord.injective e))
        · rintro ⟨y, hy, rfl⟩
          rw [inv]
          exact not_lt.2 hy.le
      have s := card_filter_add_card_filter_not (s := (univ : Finset V')) (fun x => ord x < ord (p x))
      rw [img, card_image_of_injective _ (Function.LeftInverse.injective inv), card_univ] at s
      simp only [E] at s ⊢
      omega
    have cardV : Fintype.card V' = Fintype.card (Sets (2 * k + 1) k) - R.card := by
      have c : (univ.filter (fun x : Sets (2 * k + 1) k => x ∈ V')) = univ \ R := by
        ext x; simp [V']
      rw [Fintype.card_subtype, c, card_sdiff_of_subset (subset_univ _), card_univ]
    have count : E.card = (2 * k + 1).choose k / 2 := by
      rw [← card_sets]
      omega
    let e : Fin E.card ≃ E := E.equivFin.symm
    refine ⟨E.card, fun i => (e i).1.1, fun i => (p (e i).1).1, count, ?_, ?_, ?_, ?_⟩
    · intro i j h
      exact e.injective (Subtype.ext (Subtype.ext h))
    · intro i j h
      have : p (e i).1 = p (e j).1 := Subtype.ext h
      exact e.injective (Subtype.ext (Function.LeftInverse.injective inv this))
    · intro i j h
      have h' : (e i).1 = p (e j).1 := Subtype.ext h
      have h1 := (mem_filter.1 (e i).2).2
      have h2 := (mem_filter.1 (e j).2).2
      rw [h', inv] at h1
      exact lt_asymm h2 h1
    · intro i
      have : (odd k).Adj (e i).1.1 (p (e i).1).1 := M.adj_sub (hp (e i).1)
      exact this.2
  rcases Nat.even_or_odd (Fintype.card (Sets (2 * k + 1) k)) with h | h
  · exact build ∅ (by simpa using h) (Or.inl rfl) (by rw [card_empty, Nat.even_iff.1 h])
  · have pos : 0 < Fintype.card (Sets (2 * k + 1) k) := h.pos
    obtain ⟨v⟩ := Fintype.card_pos_iff.1 pos
    refine build {v} ?_ (Or.inr ⟨v, rfl⟩) (by rw [card_singleton, Nat.odd_iff.1 h])
    rw [card_singleton]
    obtain ⟨z, hz⟩ := h
    exact ⟨z, by omega⟩

end Odd

/-- Capas estrictamente bajo la mitad. -/
def low (t : ℕ) : Finset ℕ := (range t).filter (fun j => 2 ≤ j ∧ 2 * j + 1 < t)

def mid (t : ℕ) : ℕ := if t % 2 = 1 then t.choose (t / 2) else 0

lemma identity (t : ℕ) (ht : 4 ≤ t) : 2 * (∑ j ∈ low t, t.choose j) + mid t + t.choose (t / 2) + 2 * t + 2 = 2 ^ t := by
  have first : ∀ K, 2 ≤ K → ∑ j ∈ range K, t.choose j = 1 + t + ∑ j ∈ Ico 2 K, t.choose j := by
    intro K hK
    rw [← sum_range_add_sum_Ico _ hK]
    simp [sum_range_succ]
  rcases Nat.even_or_odd' t with ⟨k, hk | hk⟩
  · have hk2 : 2 ≤ k := by omega
    have e : low t = Ico 2 k := by
      ext j
      simp only [low, mem_filter, mem_range, mem_Ico]
      omega
    have m0 : mid t = 0 := by
      rw [mid, if_neg (by omega)]
    have half : t / 2 = k := by omega
    have total : ∑ j ∈ range (t + 1), t.choose j = 2 ^ t := Nat.sum_range_choose t
    have split : ∑ j ∈ range (t + 1), t.choose j =
        2 * (∑ j ∈ range k, t.choose j) + t.choose k := by
      have a : t + 1 = (k + 1) + k := by omega
      rw [a, sum_range_add, sum_range_succ]
      have refl : ∑ x ∈ range k, t.choose (k + 1 + x) = ∑ j ∈ range k, t.choose j := by
        rw [← sum_range_reflect (fun j => t.choose j) k]
        refine sum_congr rfl (fun x hx => ?_)
        have := mem_range.1 hx
        rw [← Nat.choose_symm (by omega : k + 1 + x ≤ t)]
        congr 1
        omega
      rw [refl]
      ring
    rw [e, m0, half]
    have f := first k hk2
    omega
  · have hk2 : 2 ≤ k := by omega
    have e : low t = Ico 2 k := by
      ext j
      simp only [low, mem_filter, mem_range, mem_Ico]
      omega
    have half : t / 2 = k := by omega
    have m1 : mid t = t.choose k := by
      rw [mid, if_pos (by omega), half]
    have total : ∑ j ∈ range (t + 1), t.choose j = 2 ^ t := Nat.sum_range_choose t
    have split : ∑ j ∈ range (t + 1), t.choose j =
        2 * (∑ j ∈ range k, t.choose j) + 2 * t.choose k := by
      have a : t + 1 = (k + 1) + (k + 1) := by omega
      rw [a, sum_range_add, sum_range_succ]
      have refl : ∑ x ∈ range (k + 1), t.choose (k + 1 + x) = ∑ j ∈ range (k + 1), t.choose j := by
        rw [← sum_range_reflect (fun j => t.choose j) (k + 1)]
        refine sum_congr rfl (fun x hx => ?_)
        have := mem_range.1 hx
        rw [← Nat.choose_symm (by omega : k + 1 + x ≤ t)]
        congr 1
        omega
      rw [refl, sum_range_succ]
      ring
    rw [e, m1, half]
    have f := first k hk2
    omega

theorem main (t m : ℕ) (ht : 4 ≤ t) :
    (∃ f : Fin m × Bool → Finset (Fin t),
      Function.Injective f ∧ (∀ k, 2 ≤ (f k).card) ∧
      ∀ i, Disjoint (f (i,false)) (f (i,true)) ∧
        (univ \ (f (i,false) ∪ f (i,true))).card = 1) ↔
    2*m + Nat.choose t (t/2) + 2*t + 2 ≤ 2^t := by
  have idn := identity t ht
  have goal : (2*m + Nat.choose t (t/2) + 2*t + 2 ≤ 2^t) ↔ 2 * m ≤ 2 * (∑ j ∈ low t, t.choose j) + mid t := by omega
  rw [goal]
  constructor
  · rintro ⟨f, inj, big, pairs⟩
    let w : Finset (Fin t) → ℕ := fun S =>
      if 2 ≤ S.card ∧ 2 * S.card + 1 < t then 2 else if 2 * S.card + 1 = t then 1 else 0
    have each : ∀ i, 2 ≤ w (f (i,false)) + w (f (i,true)) := by
      intro i
      obtain ⟨dis, one⟩ := pairs i
      have a := big (i,false)
      have b := big (i,true)
      rw [card_sdiff_of_subset (subset_univ _), card_union_of_disjoint dis, card_univ, Fintype.card_fin] at one
      simp only [w]
      split_ifs <;> omega
    have lower : 2 * m ≤ ∑ p : Fin m × Bool, w (f p) := by
      rw [Fintype.sum_prod_type]
      have : ∀ i : Fin m, 2 ≤ ∑ c : Bool, w (f (i, c)) := by
        intro i
        rw [Fintype.sum_bool, add_comm]
        exact each i
      have s := sum_le_sum (s := (univ : Finset (Fin m))) (fun i _ => this i)
      simpa [mul_comm] using s
    have upper : ∑ p : Fin m × Bool, w (f p) ≤ ∑ S : Finset (Fin t), w S := by
      rw [← sum_image (s := univ) (g := f) (f := w) (fun a _ b _ h => inj h)]
      exact sum_le_sum_of_subset (subset_univ _)
    have value : ∑ S : Finset (Fin t), w S = 2 * (∑ j ∈ low t, t.choose j) + mid t := by
      have grp : ∑ S : Finset (Fin t), w S = ∑ j ∈ range (t + 1), t.choose j *
          (if 2 ≤ j ∧ 2 * j + 1 < t then 2 else if 2 * j + 1 = t then 1 else 0) := by
        rw [← powerset_univ, sum_powerset_apply_card (fun j => if 2 ≤ j ∧ 2 * j + 1 < t then 2 else if 2 * j + 1 = t then 1 else 0)]
        simp
      rw [grp]
      have split : ∀ j ∈ range (t + 1), t.choose j * (if 2 ≤ j ∧ 2 * j + 1 < t then 2 else if 2 * j + 1 = t then 1 else 0) =
          (if 2 ≤ j ∧ 2 * j + 1 < t then 2 * t.choose j else 0) + (if 2 * j + 1 = t then t.choose j else 0) := by
        intro j _
        split_ifs <;> omega
      rw [sum_congr rfl split, sum_add_distrib]
      congr 1
      · rw [← sum_filter, mul_sum]
        refine sum_congr ?_ (fun _ _ => rfl)
        ext j
        simp only [low, mem_filter, mem_range]
        omega
      · unfold mid
        split_ifs with h
        · rw [sum_eq_single (t / 2)]
          · rw [if_pos (by omega)]
          · intro j _ hj
            rw [if_neg (by omega)]
          · intro hn
            exact absurd (mem_range.2 (by omega)) hn
        · exact sum_eq_zero (fun j _ => if_neg (by omega))
    omega
  · intro hm
    have lay : ∀ j : low t, ∃ h : Sets t j.1 → Sets t (t - 1 - j.1), Function.Injective h ∧ ∀ a, Disjoint a.1 (h a).1 := by
      intro j
      exact layer t j.1 (mem_filter.1 j.2).2.2
    choose H Hinj Hdis using lay
    have middlePart : ∃ (n : ℕ) (a b : Fin n → Finset (Fin t)), n = mid t / 2 ∧ Function.Injective a ∧ Function.Injective b ∧
        (∀ i j, a i ≠ b j) ∧ (∀ i, Disjoint (a i) (b i)) ∧ (∀ i, 2 * (a i).card + 1 = t) ∧ (∀ i, 2 * (b i).card + 1 = t) := by
      by_cases h : t % 2 = 1
      · obtain ⟨k, rfl⟩ : ∃ k, t = 2 * k + 1 := ⟨t / 2, by omega⟩
        obtain ⟨n, a, b, hn, ia, ib, ab, dis⟩ := middle k (by omega)
        refine ⟨n, fun i => (a i).1, fun i => (b i).1, ?_, fun i j e => ia (Subtype.ext e),
          fun i j e => ib (Subtype.ext e), fun i j e => ab i j (Subtype.ext e), dis,
          fun i => by rw [(a i).2], fun i => by rw [(b i).2]⟩
        have half : (2 * k + 1) / 2 = k := by omega
        rw [mid, if_pos h, half]
        exact hn
      · refine ⟨0, fun i => i.elim0, fun i => i.elim0, by rw [mid, if_neg h], fun i => i.elim0, fun i => i.elim0,
          fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
    obtain ⟨n, a, b, hn, ia, ib, ab, abdis, ac, bc⟩ := middlePart
    let I := (Σ j : low t, Sets t j.1) ⊕ Fin n
    let F : I × Bool → Finset (Fin t) := fun p =>
      match p with
      | (Sum.inl x, false) => x.2.1
      | (Sum.inl x, true) => (H x.1 x.2).1
      | (Sum.inr i, false) => a i
      | (Sum.inr i, true) => b i
    have lowj : ∀ j : low t, 2 ≤ j.1 ∧ 2 * j.1 + 1 < t := fun j => (mem_filter.1 j.2).2
    have Finj : Function.Injective F := by
      have key : ∀ (x y : Σ j : low t, Sets t j.1), x.2.1 = y.2.1 → x = y := by
        rintro ⟨j, S⟩ ⟨j', S'⟩ h
        have : j = j' := by
          apply Subtype.ext
          have := congrArg card h
          rwa [S.2, S'.2] at this
        subst this
        have : S = S' := Subtype.ext h
        rw [this]
      have key2 : ∀ (x y : Σ j : low t, Sets t j.1), (H x.1 x.2).1 = (H y.1 y.2).1 → x = y := by
        rintro ⟨j, S⟩ ⟨j', S'⟩ h
        have : j = j' := by
          apply Subtype.ext
          have c := congrArg card h
          rw [(H j S).2, (H j' S').2] at c
          have := lowj j
          have := lowj j'
          omega
        subst this
        have : S = S' := Hinj j (Subtype.ext h)
        rw [this]
      rintro ⟨x | i, c⟩ ⟨y | i', c'⟩ h <;> cases c <;> cases c' <;> simp only [F] at h
      · rw [key x y h]
      · exfalso
        have e := congrArg card h
        rw [x.2.2, (H y.1 y.2).2] at e
        have := lowj x.1; have := lowj y.1; omega
      · exfalso
        have e := congrArg card h
        rw [y.2.2, (H x.1 x.2).2] at e
        have := lowj x.1; have := lowj y.1; omega
      · rw [key2 x y h]
      · exfalso
        have e := congrArg card h
        rw [x.2.2] at e
        have := lowj x.1; have := ac i'; omega
      · exfalso
        have e := congrArg card h
        rw [x.2.2] at e
        have := lowj x.1; have := bc i'; omega
      · exfalso
        have e := congrArg card h
        rw [(H x.1 x.2).2] at e
        have := lowj x.1; have := ac i'; omega
      · exfalso
        have e := congrArg card h
        rw [(H x.1 x.2).2] at e
        have := lowj x.1; have := bc i'; omega
      · exfalso
        have e := congrArg card h
        rw [y.2.2] at e
        have := lowj y.1; have := ac i; omega
      · exfalso
        have e := congrArg card h
        rw [(H y.1 y.2).2] at e
        have := lowj y.1; have := ac i; omega
      · exfalso
        have e := congrArg card h
        rw [y.2.2] at e
        have := lowj y.1; have := bc i; omega
      · exfalso
        have e := congrArg card h
        rw [(H y.1 y.2).2] at e
        have := lowj y.1; have := bc i; omega
      · rw [ia h]
      · exact absurd h (ab i i')
      · exact absurd h.symm (ab i' i)
      · rw [ib h]
    have cardI : m ≤ Fintype.card I := by
      have e : Fintype.card I = (∑ j ∈ low t, t.choose j) + n := by
        simp only [I, Fintype.card_sum, Fintype.card_sigma, card_sets, Fintype.card_fin]
        rw [sum_coe_sort (low t) (fun j => t.choose j)]
      omega
    obtain ⟨g⟩ : Nonempty (Fin m ↪ I) := Function.Embedding.nonempty_of_card_le (by simpa using cardI)
    refine ⟨fun p => F (g p.1, p.2), ?_, ?_, ?_⟩
    · intro p q h
      have := Finj h
      simp only [Prod.mk.injEq] at this
      exact Prod.ext (g.injective this.1) this.2
    · rintro ⟨i, c⟩
      show 2 ≤ (F (g i, c)).card
      rcases g i with x | j
      · cases c
        · show 2 ≤ x.2.1.card
          rw [x.2.2]; exact (lowj x.1).1
        · show 2 ≤ (H x.1 x.2).1.card
          rw [(H x.1 x.2).2]; have := lowj x.1; omega
      · cases c
        · show 2 ≤ (a j).card
          have := ac j; omega
        · show 2 ≤ (b j).card
          have := bc j; omega
    · intro i
      show Disjoint (F (g i, false)) (F (g i, true)) ∧ (univ \ (F (g i, false) ∪ F (g i, true))).card = 1
      have fin : ∀ A B : Finset (Fin t), Disjoint A B → A.card + B.card + 1 = t →
          Disjoint A B ∧ (univ \ (A ∪ B)).card = 1 := by
        intro A B h c
        refine ⟨h, ?_⟩
        rw [card_sdiff_of_subset (subset_univ _), card_union_of_disjoint h, card_univ, Fintype.card_fin]
        omega
      rcases g i with x | j
      · refine fin _ _ (Hdis x.1 x.2) ?_
        show x.2.1.card + (H x.1 x.2).1.card + 1 = t
        rw [x.2.2, (H x.1 x.2).2]; have := lowj x.1; omega
      · refine fin _ _ (abdis j) ?_
        show (a j).card + (b j).card + 1 = t
        have := ac j; have := bc j; omega

end PEqualNP.Outside.L_meta_53192

theorem PEqualNP.Outside.L_meta_53192 : ∀ (t m : Nat), 4 ≤ t →
  ((∃ f : Fin m × Bool → Finset (Fin t),
    Function.Injective f ∧ (∀ k, 2 ≤ (f k).card) ∧
    ∀ i, Disjoint (f (i,false)) (f (i,true)) ∧
      (Finset.univ \ (f (i,false) ∪ f (i,true))).card = 1) ↔
  2*m + Nat.choose t (t/2) + 2*t + 2 ≤ 2^t) := by
  intro t m ht
  convert PEqualNP.Outside.L_meta_53192.main t m ht using 8
