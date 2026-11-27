import PEqualNP.Defs

open scoped BigOperators

namespace PEqualNP.Outside.L_pcx_358_aux

abbrev XVec (n : ℕ) := Fin n → ZMod 2

def Shape (N J : Finset (List Bool)) : Prop :=
  [] ∈ N ∧ J ⊆ N ∧
  (∀ (p : List Bool) (b : Bool), p ++ [b] ∈ N → p ∈ J) ∧
  ∀ p ∈ J, p ++ [false] ∈ N ∧ p ++ [true] ∈ N

def Queries (V : Type) [AddCommGroup V] [Module (ZMod 2) V] : Set (V → Bool) :=
  {f : V → Bool | ∃ (l : V →ₗ[ZMod 2] ZMod 2) (b : ZMod 2), f = fun x => decide (l x = b)}

abbrev Reaches {V : Type} (q : List Bool → V → Bool) (p : List Bool) (x : V) : Prop :=
  ∀ j : Fin p.length, q (p.take j.val) x = p.get j

lemma zmod2_eq_zero_or_one (z : ZMod 2) : z = 0 ∨ z = 1 := by
  revert z; decide

lemma zmod2_ne_iff (z b : ZMod 2) : z ≠ b ↔ z = b + 1 := by
  revert z b; decide

lemma zmod2_decide_eq_iff (x y b : ZMod 2) : (decide (x = b) = decide (y = b)) ↔ x = y := by
  revert x y b; decide

lemma zmod2_add_self (z : ZMod 2) : z + z = 0 := by
  revert z; decide

lemma list_take_succ_eq_append {α : Type*} (p : List α) {k : ℕ} (hk : k < p.length) :
    p.take (k + 1) = p.take k ++ [p.get ⟨k, hk⟩] := by
  induction p generalizing k with
  | nil => simp at hk
  | cons a t ih =>
    cases k with
    | zero => simp
    | succ k' =>
      simp only [List.take_succ_cons, List.get_eq_getElem, List.getElem_cons_succ, List.cons_append]
      congr 1
      have hk' : k' < t.length := by simpa using hk
      have h := ih hk'
      simp [List.get_eq_getElem] at h ⊢

lemma shape_take_mem {N J : Finset (List Bool)} (hS : Shape N J) {p : List Bool} (hp : p ∈ N) :
    ∀ k ≤ p.length, p.take k ∈ N ∧ (k < p.length → p.take k ∈ J) := by
  intro k hk
  have haux : ∀ d : ℕ, ∀ k ≤ p.length, p.length - k = d →
      p.take k ∈ N ∧ (k < p.length → p.take k ∈ J) := by
    intro d
    induction d with
    | zero =>
      intro k hk hd
      have hkeq : k = p.length := by omega
      subst hkeq
      exact ⟨by simpa using hp, fun hlt => (lt_irrefl _ hlt).elim⟩
    | succ d' ih =>
      intro k hk hd
      have hlt : k < p.length := by omega
      have hsucc : p.take (k + 1) ∈ N := (ih (k + 1) (by omega) (by omega)).1
      rw [list_take_succ_eq_append p hlt] at hsucc
      have hJ : p.take k ∈ J := hS.2.2.1 (p.take k) (p.get ⟨k, hlt⟩) hsucc
      exact ⟨hS.2.1 hJ, fun _ => hJ⟩
  exact haux (p.length - k) k hk rfl

lemma reaches_append {V : Type} (q : List Bool → V → Bool) (p : List Bool) (b : Bool) (x : V)
    (hr : Reaches q p x) (hb : q p x = b) : Reaches q (p ++ [b]) x := by
  intro j
  by_cases hj : j.val < p.length
  · have ht : (p ++ [b]).take j.val = p.take j.val :=
      List.take_append_of_le_length (le_of_lt hj)
    have hg : (p ++ [b]).get j = p.get ⟨j.val, hj⟩ := by
      simp [List.get_eq_getElem, List.getElem_append_left hj]
    rw [ht, hg]
    exact hr ⟨j.val, hj⟩
  · have hjeq : j.val = p.length := by
      have hlt := j.isLt
      simp only [List.length_append, List.length_singleton] at hlt
      omega
    have ht : (p ++ [b]).take j.val = p := by
      rw [hjeq, List.take_left]
    have hg : (p ++ [b]).get j = b := by
      simp [List.get_eq_getElem, hjeq]
    rw [ht, hg]
    exact hb

lemma reaches_leaf_exists {V : Type} {N J : Finset (List Bool)} (hS : Shape N J)
    (q : List Bool → V → Bool) (x : V) :
    ∃ p ∈ N \ J, Reaches q p x := by
  have hne : (N.image List.length).Nonempty :=
    ⟨0, Finset.mem_image.mpr ⟨[], hS.1, rfl⟩⟩
  let M := (N.image List.length).max' hne
  have hleM : ∀ p ∈ N, p.length ≤ M := fun p hp =>
    Finset.le_max' (N.image List.length) p.length (Finset.mem_image.mpr ⟨p, hp, rfl⟩)
  have haux : ∀ d : ℕ, ∀ p ∈ N, M - p.length ≤ d → Reaches q p x → ∃ r ∈ N \ J, Reaches q r x := by
    intro d
    induction d with
    | zero =>
      intro p hp hd hr
      by_cases hJ : p ∈ J
      · have hnext : p ++ [q p x] ∈ N := by
          cases hq : q p x
          · exact (hS.2.2.2 p hJ).1
          · exact (hS.2.2.2 p hJ).2
        have hlen := hleM (p ++ [q p x]) hnext
        simp only [List.length_append, List.length_singleton] at hlen
        omega
      · exact ⟨p, Finset.mem_sdiff.mpr ⟨hp, hJ⟩, hr⟩
    | succ d' ih =>
      intro p hp hd hr
      by_cases hJ : p ∈ J
      · have hnext : p ++ [q p x] ∈ N := by
          cases hq : q p x
          · exact (hS.2.2.2 p hJ).1
          · exact (hS.2.2.2 p hJ).2
        have hlen : (p ++ [q p x]).length = p.length + 1 := by simp
        have hle := hleM (p ++ [q p x]) hnext
        exact ih (p ++ [q p x]) hnext (by omega) (reaches_append q p (q p x) x hr rfl)
      · exact ⟨p, Finset.mem_sdiff.mpr ⟨hp, hJ⟩, hr⟩
  refine haux M [] hS.1 (by simp) ?_
  intro j
  exact (Nat.not_lt_zero _ j.isLt).elim

lemma reaches_prefix_eq {V : Type} (q : List Bool → V → Bool) {p₁ p₂ : List Bool} {x : V}
    (h1 : Reaches q p₁ x) (h2 : Reaches q p₂ x) :
    ∀ k, k ≤ p₁.length → k ≤ p₂.length → p₁.take k = p₂.take k := by
  intro k
  induction k with
  | zero => intro _ _; simp
  | succ k' ih =>
    intro h1k h2k
    have hlt1 : k' < p₁.length := by omega
    have hlt2 : k' < p₂.length := by omega
    have hprev := ih (by omega) (by omega)
    rw [list_take_succ_eq_append p₁ hlt1, list_take_succ_eq_append p₂ hlt2, hprev]
    congr 2
    have e1 := h1 ⟨k', hlt1⟩
    have e2 := h2 ⟨k', hlt2⟩
    rw [← e1, ← e2, hprev]

lemma reaches_unique_leaf {V : Type} {N J : Finset (List Bool)} (hS : Shape N J)
    (q : List Bool → V → Bool) {p₁ p₂ : List Bool} {x : V}
    (hp1 : p₁ ∈ N \ J) (hp2 : p₂ ∈ N \ J) (h1 : Reaches q p₁ x) (h2 : Reaches q p₂ x) :
    p₁ = p₂ := by
  rcases Finset.mem_sdiff.mp hp1 with ⟨hp1N, hp1J⟩
  rcases Finset.mem_sdiff.mp hp2 with ⟨hp2N, hp2J⟩
  have hlen : p₁.length = p₂.length := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have htake := reaches_prefix_eq q h1 h2 p₁.length le_rfl (le_of_lt hlt)
      rw [List.take_length] at htake
      have hmemJ := (shape_take_mem hS hp2N p₁.length (le_of_lt hlt)).2 hlt
      rw [← htake] at hmemJ
      exact hp1J hmemJ
    · have htake := reaches_prefix_eq q h1 h2 p₂.length (le_of_lt hgt) le_rfl
      rw [List.take_length] at htake
      have hmemJ := (shape_take_mem hS hp1N p₂.length (le_of_lt hgt)).2 hgt
      rw [htake] at hmemJ
      exact hp2J hmemJ
  have htake := reaches_prefix_eq q h1 h2 p₁.length le_rfl (le_of_eq hlen)
  rw [List.take_length, hlen, List.take_length] at htake
  exact htake

lemma card_xvec (n : ℕ) : (Finset.univ : Finset (XVec n)).card = 2 ^ n := by
  simp [XVec, ZMod.card]

lemma card_filter_add_not {α : Type*} (s : Finset α) (p : α → Prop) [DecidablePred p] :
    (s.filter p).card + (s.filter (fun x => ¬ p x)).card = s.card := by
  simp only [Finset.card_filter, ← Finset.sum_add_distrib]
  trans ∑ _x ∈ s, 1
  · refine Finset.sum_congr rfl (fun x _ => ?_)
    by_cases h : p x <;> simp [h]
  · simp

lemma card_inter_ker_le {n : ℕ} : ∀ (k : ℕ) (ls : Fin k → (XVec n →ₗ[ZMod 2] ZMod 2)),
    2 ^ n ≤ 2 ^ k * (Finset.univ.filter (fun v : XVec n => ∀ j : Fin k, ls j v = 0)).card := by
  intro k
  induction k with
  | zero =>
    intro ls
    have hfilt : (Finset.univ.filter (fun v : XVec n => ∀ j : Fin 0, ls j v = 0)) = Finset.univ := by
      ext v; simp
    rw [hfilt, pow_zero, one_mul, card_xvec]
  | succ k ih =>
    intro ls
    let ls' : Fin k → (XVec n →ₗ[ZMod 2] ZMod 2) := fun j => ls j.castSucc
    let S : Finset (XVec n) := Finset.univ.filter (fun v : XVec n => ∀ j : Fin k, ls' j v = 0)
    let S0 : Finset (XVec n) := Finset.univ.filter (fun v : XVec n => ∀ j : Fin (k + 1), ls j v = 0)
    let S1 : Finset (XVec n) := S.filter (fun v => ls (Fin.last k) v ≠ 0)
    have hS0_eq : S0 = S.filter (fun v => ls (Fin.last k) v = 0) := by
      ext v
      simp only [S0, S, ls', Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h; exact ⟨fun j => h j.castSucc, h (Fin.last k)⟩
      · rintro ⟨h1, h2⟩ j
        exact Fin.lastCases h2 h1 j
    have hsplit : S.card = S0.card + S1.card := by
      rw [hS0_eq]
      exact (card_filter_add_not S (fun v => ls (Fin.last k) v = 0)).symm
    have hS1_le : S1.card ≤ S0.card := by
      by_cases hne : S1.Nonempty
      · rcases hne with ⟨w0, hw0⟩
        have hw0S : w0 ∈ S := (Finset.mem_filter.mp hw0).1
        have hw01 : ls (Fin.last k) w0 = 1 := by
          have hne0 := (Finset.mem_filter.mp hw0).2
          rcases zmod2_eq_zero_or_one (ls (Fin.last k) w0) with h0 | h1
          · exact (hne0 h0).elim
          · exact h1
        have hmaps : ∀ v ∈ S1, v + w0 ∈ S0 := by
          intro v hv
          rw [hS0_eq, Finset.mem_filter]
          have hvS : v ∈ S := (Finset.mem_filter.mp hv).1
          have hv1 : ls (Fin.last k) v = 1 := by
            have hne0 := (Finset.mem_filter.mp hv).2
            rcases zmod2_eq_zero_or_one (ls (Fin.last k) v) with h0 | h1
            · exact (hne0 h0).elim
            · exact h1
          refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun j => ?_⟩, ?_⟩
          · rw [map_add, (Finset.mem_filter.mp hvS).2 j, (Finset.mem_filter.mp hw0S).2 j, add_zero]
          · rw [map_add, hv1, hw01]
            exact zmod2_add_self 1
        have hinj : Set.InjOn (fun v : XVec n => v + w0) (S1 : Set (XVec n)) := by
          intro v1 _ v2 _ h; exact add_right_cancel h
        have hsub : S1.image (fun v => v + w0) ⊆ S0 := by
          intro x hx
          rcases Finset.mem_image.mp hx with ⟨v, hv, rfl⟩
          exact hmaps v hv
        calc S1.card = (S1.image (fun v => v + w0)).card := (Finset.card_image_of_injOn hinj).symm
          _ ≤ S0.card := Finset.card_le_card hsub
      · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
        simp
    have hih := ih ls'
    have hS_le : S.card ≤ 2 * S0.card := by omega
    calc 2 ^ n ≤ 2 ^ k * S.card := hih
      _ ≤ 2 ^ k * (2 * S0.card) := Nat.mul_le_mul_left _ hS_le
      _ = 2 ^ (k + 1) * S0.card := by rw [pow_succ]; ring

lemma reachSet_codim_bound {n : ℕ} {N J : Finset (List Bool)} (hS : Shape N J)
    {q : List Bool → XVec n → Bool} (hq : ∀ p ∈ J, q p ∈ Queries (XVec n))
    {p : List Bool} (hp : p ∈ N) {x0 : XVec n} (hx0 : Reaches q p x0) :
    2 ^ n ≤ 2 ^ p.length * (Finset.univ.filter (fun x : XVec n => Reaches q p x)).card := by
  have hex : ∀ j : Fin p.length,
      ∃ (l : XVec n →ₗ[ZMod 2] ZMod 2) (c : ZMod 2), ∀ x, q (p.take j.val) x = p.get j ↔ l x = c := by
    intro j
    have hjJ : p.take j.val ∈ J := (shape_take_mem hS hp j.val (le_of_lt j.isLt)).2 j.isLt
    rcases hq (p.take j.val) hjJ with ⟨l, b, hlb⟩
    refine ⟨l, if p.get j then b else b + 1, ?_⟩
    intro x
    rw [hlb]
    cases p.get j
    · simp only [Bool.false_eq_true, ↓reduceIte, decide_eq_false_iff_not, zmod2_ne_iff]
    · simp only [↓reduceIte, decide_eq_true_eq]
  choose l c hlc using hex
  have hlx0 : ∀ j : Fin p.length, l j x0 = c j := fun j => (hlc j x0).mp (hx0 j)
  have hcard_eq : (Finset.univ.filter (fun x : XVec n => Reaches q p x)).card =
      (Finset.univ.filter (fun v : XVec n => ∀ j : Fin p.length, l j v = 0)).card := by
    refine Finset.card_bij (fun x _ => x - x0) ?_ ?_ ?_
    · intro x hx
      have hrx : Reaches q p x := (Finset.mem_filter.mp hx).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun j => ?_⟩
      rw [map_sub, (hlc j x).mp (hrx j), hlx0 j, sub_self]
    · intro x1 _ x2 _ h; exact sub_left_inj.mp h
    · intro v hv
      have hlv : ∀ j : Fin p.length, l j v = 0 := (Finset.mem_filter.mp hv).2
      refine ⟨v + x0, ?_, add_sub_cancel_right v x0⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun j => ?_⟩
      rw [hlc j (v + x0), map_add, hlv j, hlx0 j, zero_add]
  rw [hcard_eq]
  exact card_inter_ker_le p.length l

lemma forward_dir {n m : ℕ} (f : XVec n → Fin m)
    (h2 : ∀ a : Fin m, (Finset.univ.filter (fun x : XVec n => f x = a)).card = 2)
    (mass : XVec n → ℕ) (K B : ℕ)
    (N J : Finset (List Bool)) (q : List Bool → XVec n → Bool) (out : List Bool → Fin m)
    (hS : Shape N J) (hq : ∀ p ∈ J, q p ∈ Queries (XVec n))
    (hok : ∀ p ∈ N \ J, ∀ x : XVec n, Reaches q p x → f x = out p)
    (hK : (N \ J).card ≤ K)
    (hB : (N \ J).sum (fun p => p.length * (Finset.univ.filter (fun x : XVec n => Reaches q p x)).sum mass) ≤ B) :
    ∃ R : Finset (Fin m),
      (∀ S ⊆ R, 1 < S.card →
        let directions := Submodule.span (ZMod 2)
          {z : XVec n | ∃ x y : XVec n, f x ∈ S ∧ f y = f x ∧ z = x - y}
        ∃ x y : XVec n, f x ∈ S ∧ f y ∈ S ∧ x - y ∉ directions) ∧
      2 ^ n ≤ K + R.card ∧
      n * Finset.univ.sum mass ≤ B + (Finset.univ.filter (fun x : XVec n => f x ∈ R)).sum mass := by
  let reachSet : List Bool → Finset (XVec n) := fun p => Finset.univ.filter (fun x => Reaches q p x)
  let P2 : Finset (List Bool) := (N \ J).filter (fun p => (reachSet p).card = 2)
  let R : Finset (Fin m) := P2.image out
  have hreach_sub : ∀ p ∈ N \ J, reachSet p ⊆ Finset.univ.filter (fun x => f x = out p) := by
    intro p hp x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hok p hp x (Finset.mem_filter.mp hx).2⟩
  have hreach_le2 : ∀ p ∈ N \ J, (reachSet p).card ≤ 2 := by
    intro p hp
    calc (reachSet p).card ≤ (Finset.univ.filter (fun x => f x = out p)).card :=
          Finset.card_le_card (hreach_sub p hp)
      _ = 2 := h2 (out p)
  have hP2_eq : ∀ p ∈ P2, reachSet p = Finset.univ.filter (fun x => f x = out p) := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpNJ, hcard2⟩
    exact Finset.eq_of_subset_of_card_le (hreach_sub p hpNJ) (by rw [h2 (out p), hcard2])
  have hdisj : Set.PairwiseDisjoint (↑(N \ J) : Set (List Bool)) reachSet := by
    intro p1 hp1 p2 hp2 hne
    rw [Finset.mem_coe] at hp1 hp2
    exact Finset.disjoint_left.mpr (fun x hx1 hx2 =>
      hne (reaches_unique_leaf hS q hp1 hp2
        (Finset.mem_filter.mp hx1).2 (Finset.mem_filter.mp hx2).2))
  have huniv_biUnion : (Finset.univ : Finset (XVec n)) = (N \ J).biUnion reachSet := by
    ext x
    simp only [Finset.mem_univ, Finset.mem_biUnion, reachSet, Finset.mem_filter, true_and, true_iff]
    exact reaches_leaf_exists hS q x
  have hP2_inj : Set.InjOn out (P2 : Set (List Bool)) := by
    intro p1 hp1 p2 hp2 hout
    have h1 := hP2_eq p1 hp1
    have h2' := hP2_eq p2 hp2
    rw [hout] at h1
    have heq : reachSet p1 = reachSet p2 := h1.trans h2'.symm
    have hne : (reachSet p1).Nonempty := Finset.card_pos.mp (by rw [(Finset.mem_filter.mp hp1).2]; omega)
    rcases hne with ⟨x, hx1⟩
    have hx2 : x ∈ reachSet p2 := heq ▸ hx1
    exact reaches_unique_leaf hS q (Finset.mem_filter.mp hp1).1 (Finset.mem_filter.mp hp2).1
      (Finset.mem_filter.mp hx1).2 (Finset.mem_filter.mp hx2).2
  have hR_card : R.card = P2.card := Finset.card_image_of_injOn hP2_inj
  have hR_biUnion : Finset.univ.filter (fun x : XVec n => f x ∈ R) = P2.biUnion reachSet := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, R, Finset.mem_image]
    constructor
    · rintro ⟨p, hpP2, hpout⟩
      refine ⟨p, hpP2, ?_⟩
      rw [hP2_eq p hpP2]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpout.symm⟩
    · rintro ⟨p, hpP2, hxp⟩
      rw [hP2_eq p hpP2] at hxp
      exact ⟨p, hpP2, (Finset.mem_filter.mp hxp).2.symm⟩
  refine ⟨R, ?_, ?_, ?_⟩
  · intro S hSR hScard
    dsimp only
    let L : Finset (List Bool) := P2.filter (fun p => out p ∈ S)
    have hL_of_S : ∀ a ∈ S, ∃ p ∈ L, out p = a ∧ reachSet p = Finset.univ.filter (fun x => f x = a) := by
      intro a haS
      rcases Finset.mem_image.mp (hSR haS) with ⟨p, hpP2, hpout⟩
      refine ⟨p, Finset.mem_filter.mpr ⟨hpP2, by rwa [hpout]⟩, hpout, ?_⟩
      rw [hP2_eq p hpP2, hpout]
    rcases Finset.one_lt_card.mp hScard with ⟨a1, ha1S, a2, ha2S, ha12⟩
    rcases hL_of_S a1 ha1S with ⟨p1, hp1L, hp1out, hp1eq⟩
    rcases hL_of_S a2 ha2S with ⟨p2, hp2L, hp2out, _⟩
    have hp12 : p1 ≠ p2 := fun h => ha12 (hp1out.symm.trans ((congrArg out h).trans hp2out))
    let Kset : Finset ℕ := (Finset.range (p1.length + 1)).filter (fun k => ∀ p ∈ L, p.take k = p1.take k)
    have h0K : 0 ∈ Kset := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.zero_lt_succ _), fun _ _ => rfl⟩
    let k0 : ℕ := Kset.max' ⟨0, h0K⟩
    have hk0K : k0 ∈ Kset := Finset.max'_mem Kset ⟨0, h0K⟩
    have hk0_le : k0 ≤ p1.length := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hk0K).1)
    have hk0_eq : ∀ p ∈ L, p.take k0 = p1.take k0 := (Finset.mem_filter.mp hk0K).2
    have hLNJ : ∀ p ∈ L, p ∈ N \ J := fun p hp => (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1
    have hk0_lt : ∀ p ∈ L, k0 < p.length := by
      intro p hpL
      by_contra hge
      have hle : p.length ≤ k0 := not_lt.mp hge
      have hp_take : p.take k0 = p := List.take_of_length_le hle
      have hp_eq_r : p = p1.take k0 := hp_take.symm.trans (hk0_eq p hpL)
      have hother : ∃ p' ∈ L, p' ≠ p := by
        by_cases h : p = p1
        · exact ⟨p2, hp2L, fun h2 => hp12 (h.symm.trans h2.symm)⟩
        · exact ⟨p1, hp1L, Ne.symm h⟩
      rcases hother with ⟨p', hp'L, hp'ne⟩
      have hp'_take : p'.take k0 = p := (hk0_eq p' hp'L).trans hp_eq_r.symm
      have hp_le_p' : p.length ≤ p'.length := by
        have hlen : (p'.take k0).length = p.length := congrArg List.length hp'_take
        rw [List.length_take] at hlen
        omega
      have hp_lt_p' : p.length < p'.length := by
        by_contra hnotlt
        have htake_full : p'.take k0 = p' := List.take_of_length_le (by omega)
        exact hp'ne (htake_full.symm.trans hp'_take)
      have hp_is_take : p = p'.take p.length := by
        have : (p'.take k0).take p.length = p.take p.length := congrArg (fun l => l.take p.length) hp'_take
        rw [List.take_take, min_eq_left hle, List.take_length] at this
        exact this.symm
      have hp'N : p' ∈ N := (Finset.mem_sdiff.mp (hLNJ p' hp'L)).1
      have hpJ : p ∈ J := by
        rw [hp_is_take]
        exact (shape_take_mem hS hp'N p.length (le_of_lt hp_lt_p')).2 hp_lt_p'
      exact (Finset.mem_sdiff.mp (hLNJ p hpL)).2 hpJ
    have hrJ : p1.take k0 ∈ J :=
      (shape_take_mem hS (Finset.mem_sdiff.mp (hLNJ p1 hp1L)).1 k0 hk0_le).2 (hk0_lt p1 hp1L)
    rcases hq (p1.take k0) hrJ with ⟨h, b, hqb⟩
    have hconst : ∀ x y : XVec n, f x ∈ S → f y = f x → h x = h y := by
      intro x y hfxS hfy
      rcases hL_of_S (f x) hfxS with ⟨p, hpL, _, hpeq⟩
      have hrx : Reaches q p x := by
        have hx : x ∈ reachSet p := hpeq.symm ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
        exact (Finset.mem_filter.mp hx).2
      have hry : Reaches q p y := by
        have hy : y ∈ reachSet p := hpeq.symm ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfy⟩
        exact (Finset.mem_filter.mp hy).2
      have hk0p : k0 < p.length := hk0_lt p hpL
      have ex := hrx ⟨k0, hk0p⟩
      have ey := hry ⟨k0, hk0p⟩
      rw [hk0_eq p hpL, hqb] at ex ey
      dsimp only at ex ey
      exact (zmod2_decide_eq_iff (h x) (h y) b).mp (ex.trans ey.symm)
    have hvanish : ∀ z ∈ Submodule.span (ZMod 2)
        {z : XVec n | ∃ x y : XVec n, f x ∈ S ∧ f y = f x ∧ z = x - y}, h z = 0 := by
      intro z hz
      refine Submodule.span_induction ?_ (map_zero h) (fun u v _ _ hu hv => by rw [map_add, hu, hv, add_zero])
        (fun c u _ hu => by rw [map_smul, hu, smul_zero]) hz
      rintro w ⟨x, y, hfxS, hfy, rfl⟩
      rw [map_sub, hconst x y hfxS hfy, sub_self]
    have hnotK : k0 + 1 ∉ Kset := fun hm =>
      Nat.not_lt_of_le (Finset.le_max' Kset (k0 + 1) hm) (Nat.lt_succ_self k0)
    have hrange : k0 + 1 ∈ Finset.range (p1.length + 1) :=
      Finset.mem_range.mpr (Nat.add_lt_add_right (hk0_lt p1 hp1L) 1)
    have hnotall : ¬ ∀ p ∈ L, p.take (k0 + 1) = p1.take (k0 + 1) :=
      fun hall => hnotK (Finset.mem_filter.mpr ⟨hrange, hall⟩)
    push Not at hnotall
    rcases hnotall with ⟨p3, hp3L, hp3ne⟩
    have hk0_1 : k0 < p1.length := hk0_lt p1 hp1L
    have hk0_3 : k0 < p3.length := hk0_lt p3 hp3L
    have hbit_ne : p3.get ⟨k0, hk0_3⟩ ≠ p1.get ⟨k0, hk0_1⟩ := by
      intro heq
      apply hp3ne
      rw [list_take_succ_eq_append p3 hk0_3, list_take_succ_eq_append p1 hk0_1, hk0_eq p3 hp3L, heq]
    have hp1_ne : (reachSet p1).Nonempty := Finset.card_pos.mp (by rw [(Finset.mem_filter.mp (Finset.mem_filter.mp hp1L).1).2]; omega)
    have hp3_ne : (reachSet p3).Nonempty := Finset.card_pos.mp (by rw [(Finset.mem_filter.mp (Finset.mem_filter.mp hp3L).1).2]; omega)
    rcases hp1_ne with ⟨x, hxp1⟩
    rcases hp3_ne with ⟨y, hyp3⟩
    have hfx : f x = out p1 := hok p1 (hLNJ p1 hp1L) x (Finset.mem_filter.mp hxp1).2
    have hfy : f y = out p3 := hok p3 (hLNJ p3 hp3L) y (Finset.mem_filter.mp hyp3).2
    have ex := (Finset.mem_filter.mp hxp1).2 ⟨k0, hk0_1⟩
    have ey := (Finset.mem_filter.mp hyp3).2 ⟨k0, hk0_3⟩
    rw [hqb] at ex
    rw [hk0_eq p3 hp3L, hqb] at ey
    dsimp only at ex ey
    refine ⟨x, y, by rw [hfx, hp1out]; exact ha1S, by rw [hfy]; exact (Finset.mem_filter.mp hp3L).2, ?_⟩
    intro hmem
    have h0 : h (x - y) = 0 := hvanish (x - y) hmem
    have hxy : h x = h y := sub_eq_zero.mp (by rwa [map_sub] at h0)
    apply hbit_ne
    rw [← ey, ← ex, hxy]
  · have hsum_card : 2 ^ n = (N \ J).sum (fun p => (reachSet p).card) := by
      rw [← card_xvec n, huniv_biUnion, Finset.card_biUnion hdisj]
    have hbound : (N \ J).sum (fun p => (reachSet p).card) ≤
        (N \ J).sum (fun p => 1 + if (reachSet p).card = 2 then 1 else 0) := by
      apply Finset.sum_le_sum
      intro p hp
      have hle := hreach_le2 p hp
      split_ifs <;> omega
    rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one,
      ← Finset.card_filter] at hbound
    rw [hsum_card, hR_card]
    exact hbound.trans (Nat.add_le_add_right hK _)
  · have hsum_mass : Finset.univ.sum mass = (N \ J).sum (fun p => (reachSet p).sum mass) := by
      conv_lhs => rw [huniv_biUnion]
      exact Finset.sum_biUnion hdisj
    have hR_mass : (Finset.univ.filter (fun x : XVec n => f x ∈ R)).sum mass =
        P2.sum (fun p => (reachSet p).sum mass) := by
      rw [hR_biUnion]
      refine Finset.sum_biUnion ?_
      intro p1 hp1 p2 hp2 hne
      rw [Finset.mem_coe] at hp1 hp2
      exact hdisj (Finset.mem_coe.mpr (Finset.mem_filter.mp hp1).1)
        (Finset.mem_coe.mpr (Finset.mem_filter.mp hp2).1) hne
    have hterm : ∀ p ∈ N \ J,
        n * (reachSet p).sum mass ≤
        p.length * (reachSet p).sum mass +
        (if (reachSet p).card = 2 then (reachSet p).sum mass else 0) := by
      intro p hp
      have hle2 := hreach_le2 p hp
      by_cases h0 : (reachSet p).card = 0
      · have hempty : reachSet p = ∅ := Finset.card_eq_zero.mp h0
        simp [hempty]
      · have hne : (reachSet p).Nonempty := Finset.card_pos.mp (Nat.pos_of_ne_zero h0)
        rcases hne with ⟨x0, hx0⟩
        have hcod := reachSet_codim_bound hS hq (Finset.mem_sdiff.mp hp).1 (Finset.mem_filter.mp hx0).2
        by_cases h2c : (reachSet p).card = 2
        · simp only [h2c, ↓reduceIte]
          have hpow : 2 ^ n ≤ 2 ^ (p.length + 1) := by
            rw [h2c] at hcod
            simpa [pow_succ] using hcod
          have hlen : n ≤ p.length + 1 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hpow
          have hmul : n * (reachSet p).sum mass ≤ (p.length + 1) * (reachSet p).sum mass :=
            Nat.mul_le_mul_right _ hlen
          linarith
        · simp only [h2c, ↓reduceIte, add_zero]
          have h1c : (reachSet p).card = 1 := by omega
          rw [h1c, mul_one] at hcod
          have hlen : n ≤ p.length := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hcod
          exact Nat.mul_le_mul_right _ hlen
    have hsum_ineq : n * Finset.univ.sum mass ≤
        (N \ J).sum (fun p => p.length * (reachSet p).sum mass) +
        (N \ J).sum (fun p => if (reachSet p).card = 2 then (reachSet p).sum mass else 0) := by
      rw [hsum_mass, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum hterm
    have hfilt_sum : (N \ J).sum (fun p => if (reachSet p).card = 2 then (reachSet p).sum mass else 0) =
        P2.sum (fun p => (reachSet p).sum mass) := by
      rw [← Finset.sum_filter]
    rw [hR_mass, ← hfilt_sum]
    exact hsum_ineq.trans (Nat.add_le_add_right hB _)

inductive ATree (n m : ℕ) : Type
  | leaf (o : Fin m) : ATree n m
  | node (l : XVec n →ₗ[ZMod 2] ZMod 2) (b : ZMod 2) (left right : ATree n m) : ATree n m

namespace ATree

def nodes {n m : ℕ} : ATree n m → Finset (List Bool)
  | leaf _ => {[]}
  | node _ _ L R => insert [] ((L.nodes.image (false :: ·)) ∪ (R.nodes.image (true :: ·)))

def internal {n m : ℕ} : ATree n m → Finset (List Bool)
  | leaf _ => ∅
  | node _ _ L R => insert [] ((L.internal.image (false :: ·)) ∪ (R.internal.image (true :: ·)))

def leaves {n m : ℕ} : ATree n m → Finset (List Bool)
  | leaf _ => {[]}
  | node _ _ L R => (L.leaves.image (false :: ·)) ∪ (R.leaves.image (true :: ·))

def query {n m : ℕ} : ATree n m → List Bool → XVec n → Bool
  | leaf _ => fun _ _ => false
  | node l b L R => fun p x =>
      match p with
      | [] => decide (l x = b)
      | false :: p' => L.query p' x
      | true :: p' => R.query p' x

def out {n m : ℕ} : ATree n m → List Bool → Fin m
  | leaf o => fun _ => o
  | node _ _ L R => fun p =>
      match p with
      | [] => L.out []
      | false :: p' => L.out p'
      | true :: p' => R.out p'

def eval {n m : ℕ} : ATree n m → XVec n → Fin m
  | leaf o => fun _ => o
  | node l b L R => fun x => if decide (l x = b) then R.eval x else L.eval x

lemma nil_mem_nodes {n m : ℕ} (t : ATree n m) : [] ∈ t.nodes := by
  cases t <;> simp [nodes]

lemma internal_sub_nodes {n m : ℕ} (t : ATree n m) : t.internal ⊆ t.nodes := by
  induction t with
  | leaf _ => simp [internal]
  | node _ _ L R ihL ihR =>
    intro p hp
    simp only [internal, nodes, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hp ⊢
    rcases hp with rfl | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨q, ihL hq, rfl⟩)
    · exact Or.inr (Or.inr ⟨q, ihR hq, rfl⟩)

lemma nodes_sdiff_internal {n m : ℕ} (t : ATree n m) : t.nodes \ t.internal = t.leaves := by
  induction t with
  | leaf _ => simp [nodes, internal, leaves]
  | node _ _ L R ihL ihR =>
    ext p
    simp only [Finset.mem_sdiff, nodes, internal, leaves, Finset.mem_insert, Finset.mem_union,
      Finset.mem_image]
    cases p with
    | nil => simp
    | cons b p' =>
      cases b
      · constructor
        · rintro ⟨h1, h2⟩
          rcases h1 with h | ⟨q, hq, hqeq⟩ | ⟨q, _, hqeq⟩
          · exact (List.cons_ne_nil _ _ h).elim
          · injection hqeq with _ hqp
            subst hqp
            left
            refine ⟨q, ?_, rfl⟩
            rw [← ihL]
            refine Finset.mem_sdiff.mpr ⟨hq, fun hqI => h2 ?_⟩
            exact Or.inr (Or.inl ⟨q, hqI, rfl⟩)
          · injection hqeq with hb _
            exact (Bool.false_ne_true hb.symm).elim
        · rintro (⟨q, hq, hqeq⟩ | ⟨q, _, hqeq⟩)
          · injection hqeq with _ hqp
            subst hqp
            rw [← ihL, Finset.mem_sdiff] at hq
            refine ⟨Or.inr (Or.inl ⟨q, hq.1, rfl⟩), ?_⟩
            rintro (h | ⟨r, hr, hreq⟩ | ⟨r, _, hreq⟩)
            · exact List.cons_ne_nil _ _ h
            · injection hreq with _ hrp; subst hrp; exact hq.2 hr
            · injection hreq with hb _; exact Bool.false_ne_true hb.symm
          · injection hqeq with hb _; exact (Bool.false_ne_true hb.symm).elim
      · constructor
        · rintro ⟨h1, h2⟩
          rcases h1 with h | ⟨q, _, hqeq⟩ | ⟨q, hq, hqeq⟩
          · exact (List.cons_ne_nil _ _ h).elim
          · injection hqeq with hb _; exact (Bool.false_ne_true hb).elim
          · injection hqeq with _ hqp
            subst hqp
            right
            refine ⟨q, ?_, rfl⟩
            rw [← ihR]
            refine Finset.mem_sdiff.mpr ⟨hq, fun hqI => h2 ?_⟩
            exact Or.inr (Or.inr ⟨q, hqI, rfl⟩)
        · rintro (⟨q, _, hqeq⟩ | ⟨q, hq, hqeq⟩)
          · injection hqeq with hb _; exact (Bool.false_ne_true hb).elim
          · injection hqeq with _ hqp
            subst hqp
            rw [← ihR, Finset.mem_sdiff] at hq
            refine ⟨Or.inr (Or.inr ⟨q, hq.1, rfl⟩), ?_⟩
            rintro (h | ⟨r, _, hreq⟩ | ⟨r, hr, hreq⟩)
            · exact List.cons_ne_nil _ _ h
            · injection hreq with hb _; exact Bool.false_ne_true hb
            · injection hreq with _ hrp; subst hrp; exact hq.2 hr

lemma shape_ok {n m : ℕ} (t : ATree n m) : Shape t.nodes t.internal := by
  induction t with
  | leaf _ =>
    refine ⟨by simp [nodes], by simp [internal], ?_, ?_⟩
    · intro p b hp
      simp only [nodes, Finset.mem_singleton] at hp
      exact (List.append_ne_nil_of_right_ne_nil p (List.cons_ne_nil b []) hp).elim
    · intro p hp
      simp [internal] at hp
  | node _ _ L R ihL ihR =>
    refine ⟨nil_mem_nodes _, internal_sub_nodes _, ?_, ?_⟩
    · intro p b hp
      simp only [nodes, internal, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hp ⊢
      cases p with
      | nil => exact Or.inl rfl
      | cons c p' =>
        cases c
        · rcases hp with h | ⟨q, hq, hqeq⟩ | ⟨q, _, hqeq⟩
          · exact (List.cons_ne_nil _ _ h).elim
          · simp only [List.cons_append] at hqeq
            injection hqeq with _ hqp
            exact Or.inr (Or.inl ⟨p', ihL.2.2.1 p' b (by rwa [← hqp]), rfl⟩)
          · simp only [List.cons_append] at hqeq
            injection hqeq with hb _
            exact (Bool.false_ne_true hb.symm).elim
        · rcases hp with h | ⟨q, _, hqeq⟩ | ⟨q, hq, hqeq⟩
          · exact (List.cons_ne_nil _ _ h).elim
          · simp only [List.cons_append] at hqeq
            injection hqeq with hb _
            exact (Bool.false_ne_true hb).elim
          · simp only [List.cons_append] at hqeq
            injection hqeq with _ hqp
            exact Or.inr (Or.inr ⟨p', ihR.2.2.1 p' b (by rwa [← hqp]), rfl⟩)
    · intro p hp
      simp only [nodes, internal, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hp ⊢
      rcases hp with rfl | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
      · constructor
        · exact Or.inr (Or.inl ⟨[], nil_mem_nodes L, rfl⟩)
        · exact Or.inr (Or.inr ⟨[], nil_mem_nodes R, rfl⟩)
      · constructor
        · exact Or.inr (Or.inl ⟨q ++ [false], (ihL.2.2.2 q hq).1, rfl⟩)
        · exact Or.inr (Or.inl ⟨q ++ [true], (ihL.2.2.2 q hq).2, rfl⟩)
      · constructor
        · exact Or.inr (Or.inr ⟨q ++ [false], (ihR.2.2.2 q hq).1, rfl⟩)
        · exact Or.inr (Or.inr ⟨q ++ [true], (ihR.2.2.2 q hq).2, rfl⟩)

lemma queries_ok {n m : ℕ} (t : ATree n m) : ∀ p ∈ t.internal, t.query p ∈ Queries (XVec n) := by
  induction t with
  | leaf _ => intro p hp; simp [internal] at hp
  | node l b L R ihL ihR =>
    intro p hp
    simp only [internal, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hp
    rcases hp with rfl | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
    · exact ⟨l, b, rfl⟩
    · exact ihL q hq
    · exact ihR q hq

lemma reaches_out {n m : ℕ} (t : ATree n m) :
    ∀ p ∈ t.leaves, ∀ x : XVec n, Reaches t.query p x → t.out p = t.eval x := by
  induction t with
  | leaf o =>
    intro p hp x _
    simp only [leaves, Finset.mem_singleton] at hp
    subst hp
    rfl
  | node l b L R ihL ihR =>
    intro p hp x hrx
    simp only [leaves, Finset.mem_union, Finset.mem_image] at hp
    rcases hp with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
    · have h0 : decide (l x = b) = false := by
        simpa [query] using hrx ⟨0, Nat.zero_lt_succ _⟩
      have hrq : Reaches L.query q x := by
        intro j
        simpa [query] using hrx ⟨j.val + 1, Nat.add_lt_add_right j.isLt 1⟩
      simp only [out, eval, h0, Bool.false_eq_true, ↓reduceIte]
      exact ihL q hq x hrq
    · have h0 : decide (l x = b) = true := by
        simpa [query] using hrx ⟨0, Nat.zero_lt_succ _⟩
      have hrq : Reaches R.query q x := by
        intro j
        simpa [query] using hrx ⟨j.val + 1, Nat.add_lt_add_right j.isLt 1⟩
      simp only [out, eval, h0, ↓reduceIte]
      exact ihR q hq x hrq

lemma leaves_card_node {n m : ℕ} (l : XVec n →ₗ[ZMod 2] ZMod 2) (b : ZMod 2) (L R : ATree n m) :
    (node l b L R).leaves.card = L.leaves.card + R.leaves.card := by
  dsimp only [leaves]
  have hdisj : Disjoint (L.leaves.image (false :: ·)) (R.leaves.image (true :: ·)) := by
    rw [Finset.disjoint_left]
    intro p hpL hpR
    rcases Finset.mem_image.mp hpL with ⟨q1, _, h1⟩
    rcases Finset.mem_image.mp hpR with ⟨q2, _, h2⟩
    have h12 := h1.trans h2.symm
    injection h12 with hb _
    exact Bool.false_ne_true hb
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective, Finset.card_image_of_injective]
  · intro p1 p2 h; injection h
  · intro p1 p2 h; injection h

lemma reaches_node_false {n m : ℕ} (l : XVec n →ₗ[ZMod 2] ZMod 2) (b : ZMod 2) (L R : ATree n m)
    (q : List Bool) (x : XVec n) :
    Reaches (node l b L R).query (false :: q) x ↔ l x ≠ b ∧ Reaches L.query q x := by
  constructor
  · intro h
    have h0 : decide (l x = b) = false := by simpa [query] using h ⟨0, Nat.zero_lt_succ _⟩
    refine ⟨decide_eq_false_iff_not.mp h0, ?_⟩
    intro j
    simpa [query] using h ⟨j.val + 1, Nat.add_lt_add_right j.isLt 1⟩
  · rintro ⟨hne, hq⟩ j
    cases hj : j.val with
    | zero =>
      have : j = ⟨0, Nat.zero_lt_succ _⟩ := Fin.ext hj
      subst this
      simpa [query] using decide_eq_false hne
    | succ j' =>
      have hlt : j' < q.length := by have := j.isLt; simp only [List.length_cons] at this; omega
      have : j = ⟨j' + 1, Nat.add_lt_add_right hlt 1⟩ := Fin.ext hj
      subst this
      simpa [query] using hq ⟨j', hlt⟩

lemma reaches_node_true {n m : ℕ} (l : XVec n →ₗ[ZMod 2] ZMod 2) (b : ZMod 2) (L R : ATree n m)
    (q : List Bool) (x : XVec n) :
    Reaches (node l b L R).query (true :: q) x ↔ l x = b ∧ Reaches R.query q x := by
  constructor
  · intro h
    have h0 : decide (l x = b) = true := by simpa [query] using h ⟨0, Nat.zero_lt_succ _⟩
    refine ⟨decide_eq_true_eq.mp h0, ?_⟩
    intro j
    simpa [query] using h ⟨j.val + 1, Nat.add_lt_add_right j.isLt 1⟩
  · rintro ⟨heq, hq⟩ j
    cases hj : j.val with
    | zero =>
      have : j = ⟨0, Nat.zero_lt_succ _⟩ := Fin.ext hj
      subst this
      simpa [query] using decide_eq_true heq
    | succ j' =>
      have hlt : j' < q.length := by have := j.isLt; simp only [List.length_cons] at this; omega
      have : j = ⟨j' + 1, Nat.add_lt_add_right hlt 1⟩ := Fin.ext hj
      subst this
      simpa [query] using hq ⟨j', hlt⟩

lemma sum_leaves_mass {n m : ℕ} (t : ATree n m) (H : Finset (XVec n)) (mass : XVec n → ℕ) :
    t.leaves.sum (fun p => (H.filter (fun x => Reaches t.query p x)).sum mass) = H.sum mass := by
  have hdisj : Set.PairwiseDisjoint (↑t.leaves : Set (List Bool))
      (fun p => H.filter (fun x => Reaches t.query p x)) := by
    intro p1 hp1 p2 hp2 hne
    rw [Finset.mem_coe, ← t.nodes_sdiff_internal] at hp1 hp2
    exact Finset.disjoint_left.mpr (fun x hx1 hx2 =>
      hne (reaches_unique_leaf t.shape_ok t.query hp1 hp2
        (Finset.mem_filter.mp hx1).2 (Finset.mem_filter.mp hx2).2))
  have hbi : t.leaves.biUnion (fun p => H.filter (fun x => Reaches t.query p x)) = H := by
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_filter]
    constructor
    · rintro ⟨_, _, hxH, _⟩; exact hxH
    · intro hxH
      rcases reaches_leaf_exists t.shape_ok t.query x with ⟨p, hpNJ, hpx⟩
      rw [t.nodes_sdiff_internal] at hpNJ
      exact ⟨p, hpNJ, hxH, hpx⟩
  rw [← Finset.sum_biUnion hdisj, hbi]

end ATree

def projLM {n : ℕ} (i : Fin n) : XVec n →ₗ[ZMod 2] ZMod 2 where
  toFun x := x i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def dotLM {n : ℕ} (c : XVec n) : XVec n →ₗ[ZMod 2] ZMod 2 where
  toFun x := dotProduct c x
  map_add' x y := dotProduct_add c x y
  map_smul' a x := by simp [dotProduct_smul]

lemma exists_dual_sep {n : ℕ} (W : Submodule (ZMod 2) (XVec n)) {v : XVec n} (hvW : v ∉ W) :
    ∃ h : XVec n →ₗ[ZMod 2] ZMod 2, (∀ w ∈ W, h w = 0) ∧ h v = 1 := by
  have hv0 : v ≠ 0 := fun h => hvW (h ▸ W.zero_mem)
  let Kv : Submodule (ZMod 2) (XVec n) := Submodule.span (ZMod 2) {v}
  let S : Submodule (ZMod 2) (XVec n) := W ⊔ Kv
  rcases Submodule.exists_isCompl S with ⟨T, hST⟩
  have hcomp : IsCompl Kv (W ⊔ T) := by
    constructor
    · rw [Submodule.disjoint_def]
      intro x hxK hxWT
      rcases Submodule.mem_span_singleton.mp hxK with ⟨a, rfl⟩
      rcases Submodule.mem_sup.mp hxWT with ⟨w, hw, t, ht, hwt⟩
      have htS : t ∈ S := by
        have h1 : a • v - w = t := by rw [← hwt]; abel
        rw [← h1]
        exact S.sub_mem (Submodule.mem_sup_right (Submodule.smul_mem Kv a (Submodule.subset_span rfl)))
          (Submodule.mem_sup_left hw)
      have ht0 : t = 0 := Submodule.disjoint_def.mp hST.disjoint t htS ht
      rw [ht0, add_zero] at hwt
      rcases zmod2_eq_zero_or_one a with rfl | rfl
      · simp
      · rw [one_smul] at hwt
        exact (hvW (hwt ▸ hw)).elim
    · rw [codisjoint_iff]
      calc Kv ⊔ (W ⊔ T) = (W ⊔ Kv) ⊔ T := by rw [← sup_assoc, sup_comm Kv W]
        _ = S ⊔ T := rfl
        _ = ⊤ := hST.sup_eq_top
  let proj : XVec n →ₗ[ZMod 2] Kv := Submodule.projectionOnto Kv (W ⊔ T) hcomp
  let l : XVec n →ₗ[ZMod 2] ZMod 2 :=
    (LinearEquiv.toSpanNonzeroSingleton (ZMod 2) (XVec n) v hv0).symm.toLinearMap.comp proj
  refine ⟨l, ?_, ?_⟩
  · intro w hw
    dsimp only [l, LinearMap.comp_apply, proj]
    have hp0 : Submodule.projectionOnto Kv (W ⊔ T) hcomp w = 0 :=
      Submodule.projectionOnto_apply_right hcomp ⟨w, Submodule.mem_sup_left hw⟩
    rw [hp0, map_zero]
  · dsimp only [l, LinearMap.comp_apply, proj]
    have hvK : v ∈ Kv := Submodule.subset_span rfl
    have hpv : Submodule.projectionOnto Kv (W ⊔ T) hcomp v = ⟨v, hvK⟩ :=
      Submodule.projectionOnto_apply_left hcomp ⟨v, hvK⟩
    rw [hpv]
    have h1 : (⟨v, hvK⟩ : Kv) = LinearEquiv.toSpanNonzeroSingleton (ZMod 2) (XVec n) v hv0 1 := by
      apply Subtype.ext
      simp
    change (LinearEquiv.toSpanNonzeroSingleton (ZMod 2) (XVec n) v hv0).symm ⟨v, hvK⟩ = 1
    rw [h1, LinearEquiv.symm_apply_apply]

noncomputable def subFinset {n : ℕ} (W : Submodule (ZMod 2) (XVec n)) : Finset (XVec n) :=
  @Finset.filter (XVec n) (fun v => v ∈ W) (Classical.decPred _) Finset.univ

noncomputable def cosetFinset {n : ℕ} (W : Submodule (ZMod 2) (XVec n)) (x0 : XVec n) : Finset (XVec n) :=
  @Finset.filter (XVec n) (fun x => x - x0 ∈ W) (Classical.decPred _) Finset.univ

lemma mem_subFinset {n : ℕ} {W : Submodule (ZMod 2) (XVec n)} {v : XVec n} :
    v ∈ subFinset W ↔ v ∈ W := by
  simp [subFinset]

lemma mem_cosetFinset {n : ℕ} {W : Submodule (ZMod 2) (XVec n)} {x0 x : XVec n} :
    x ∈ cosetFinset W x0 ↔ x - x0 ∈ W := by
  simp [cosetFinset]

lemma sub_ker_card_half {n : ℕ} (W : Submodule (ZMod 2) (XVec n))
    (h : XVec n →ₗ[ZMod 2] ZMod 2) {w0 : XVec n} (hw0W : w0 ∈ W) (hw0h : h w0 = 1) :
    (subFinset W).card = 2 * (subFinset (W ⊓ LinearMap.ker h)).card := by
  let SW := subFinset W
  let S0 := SW.filter (fun v => h v = 0)
  let S1 := SW.filter (fun v => h v ≠ 0)
  have hS0_eq : subFinset (W ⊓ LinearMap.ker h) = S0 := by
    ext v
    simp [SW, S0, mem_subFinset, Submodule.mem_inf, LinearMap.mem_ker]
  have hsplit : SW.card = S0.card + S1.card :=
    (card_filter_add_not SW (fun v => h v = 0)).symm
  have hcard_eq : S1.card = S0.card := by
    refine Finset.card_bij (fun v _ => v + w0) ?_ ?_ ?_
    · intro v hv
      rcases Finset.mem_filter.mp hv with ⟨hvW, hvh⟩
      have hv1 : h v = 1 := by
        rcases zmod2_eq_zero_or_one (h v) with h0 | h1
        · exact (hvh h0).elim
        · exact h1
      refine Finset.mem_filter.mpr ⟨mem_subFinset.mpr (W.add_mem (mem_subFinset.mp hvW) hw0W), ?_⟩
      rw [map_add, hv1, hw0h]
      exact zmod2_add_self 1
    · intro v1 _ v2 _ heq; exact add_right_cancel heq
    · intro u hu
      rcases Finset.mem_filter.mp hu with ⟨huW, huh⟩
      refine ⟨u + w0, ?_, ?_⟩
      · refine Finset.mem_filter.mpr ⟨mem_subFinset.mpr (W.add_mem (mem_subFinset.mp huW) hw0W), ?_⟩
        rw [map_add, huh, hw0h, zero_add]
        exact one_ne_zero
      · rw [add_assoc]
        have hw00 : w0 + w0 = 0 := by ext i; exact zmod2_add_self (w0 i)
        rw [hw00, add_zero]
  rw [hS0_eq, hsplit, hcard_eq, two_mul]

lemma card_coset_eq {n : ℕ} (W : Submodule (ZMod 2) (XVec n)) (x0 : XVec n) :
    (cosetFinset W x0).card = (subFinset W).card := by
  refine Finset.card_bij (fun x _ => x - x0) ?_ ?_ ?_
  · intro x hx; exact mem_subFinset.mpr (mem_cosetFinset.mp hx)
  · intro x1 _ x2 _ h; exact sub_left_inj.mp h
  · intro v hv
    refine ⟨v + x0, ?_, add_sub_cancel_right v x0⟩
    exact mem_cosetFinset.mpr (by simpa using mem_subFinset.mp hv)

lemma card_span_singleton_le_two {n : ℕ} (v : XVec n) :
    (subFinset (Submodule.span (ZMod 2) {v})).card ≤ 2 := by
  have hsub : subFinset (Submodule.span (ZMod 2) {v}) ⊆ ({0, v} : Finset (XVec n)) := by
    intro x hx
    rcases Submodule.mem_span_singleton.mp (mem_subFinset.mp hx) with ⟨a, rfl⟩
    rcases zmod2_eq_zero_or_one a with rfl | rfl
    · simp
    · simp
  exact (Finset.card_le_card hsub).trans (Finset.card_le_two)

lemma build_pair_tree {n m : ℕ} (f : XVec n → Fin m)
    (h2 : ∀ a : Fin m, (Finset.univ.filter (fun x : XVec n => f x = a)).card = 2)
    (mass : XVec n → ℕ) (R : Finset (Fin m))
    (hRsep : ∀ S ⊆ R, 1 < S.card →
      let directions := Submodule.span (ZMod 2)
        {z : XVec n | ∃ x y : XVec n, f x ∈ S ∧ f y = f x ∧ z = x - y}
      ∃ x y : XVec n, f x ∈ S ∧ f y ∈ S ∧ x - y ∉ directions) :
    ∀ (d : ℕ) (W : Submodule (ZMod 2) (XVec n)) (x0 : XVec n),
      (subFinset W).card = 2 ^ d →
      let H : Finset (XVec n) := cosetFinset W x0
      let RH : Finset (Fin m) := R.filter (fun a => ∀ x : XVec n, f x = a → x ∈ H)
      (∀ a ∈ R, (∀ x : XVec n, f x = a → x ∈ H) ∨ (∀ x : XVec n, f x = a → x ∉ H)) →
      ∃ t : ATree n m,
        (∀ x ∈ H, t.eval x = f x) ∧
        t.leaves.card + RH.card = 2 ^ d ∧
        t.leaves.sum (fun p => p.length * (H.filter (fun x => Reaches t.query p x)).sum mass) +
          (H.filter (fun x => f x ∈ RH)).sum mass = d * H.sum mass := by
  intro d
  induction d with
  | zero =>
    intro W x0 hWcard H RH _
    have hHcard : H.card = 1 := by
      dsimp only [H]; rw [card_coset_eq W x0, hWcard, pow_zero]
    have hx0H : x0 ∈ H := mem_cosetFinset.mpr (by simp [W.zero_mem])
    have hHeq : H = {x0} := Finset.eq_singleton_iff_unique_mem.mpr ⟨hx0H, fun y hy => by
      rcases Finset.card_eq_one.mp hHcard with ⟨z, hz⟩
      rw [hz, Finset.mem_singleton] at hx0H hy
      exact hy.trans hx0H.symm⟩
    have hRHempty : RH = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro a ha
      have hsub : Finset.univ.filter (fun x => f x = a) ⊆ H := fun x hx =>
        (Finset.mem_filter.mp ha).2 x (Finset.mem_filter.mp hx).2
      have hle := Finset.card_le_card hsub
      rw [h2 a, hHcard] at hle
      omega
    refine ⟨ATree.leaf (f x0), ?_, ?_, ?_⟩
    · intro x hx
      rw [hHeq, Finset.mem_singleton] at hx
      subst hx; rfl
    · rw [hRHempty]; simp [ATree.leaves]
    · rw [hRHempty]; simp [ATree.leaves]
  | succ d' ih =>
    intro W x0 hWcard H RH hclosed
    have hHcard : H.card = 2 ^ (d' + 1) := by
      dsimp only [H]; rw [card_coset_eq W x0, hWcard]
    by_cases hbase : d' = 0 ∧ RH.card = 1
    · rcases hbase with ⟨rfl, hRH1⟩
      rcases Finset.card_eq_one.mp hRH1 with ⟨a, hRHa⟩
      have hsub : Finset.univ.filter (fun x => f x = a) ⊆ H := fun x hx => by
        have haRH : a ∈ RH := by rw [hRHa]; simp
        exact (Finset.mem_filter.mp haRH).2 x (Finset.mem_filter.mp hx).2
      have hHeq : Finset.univ.filter (fun x => f x = a) = H :=
        Finset.eq_of_subset_of_card_le hsub (by rw [hHcard, h2 a]; norm_num)
      refine ⟨ATree.leaf a, ?_, ?_, ?_⟩
      · intro x hx
        rw [← hHeq] at hx
        exact (Finset.mem_filter.mp hx).2.symm
      · rw [hRHa]; simp [ATree.leaves]
      · have hfilt : H.filter (fun x => f x ∈ RH) = H := by
          ext x
          simp only [Finset.mem_filter, and_iff_left_iff_imp]
          intro hx
          rw [← hHeq] at hx
          rw [hRHa, Finset.mem_singleton]
          exact (Finset.mem_filter.mp hx).2
        rw [hfilt]; simp [ATree.leaves]
    · have hex_h : ∃ h : XVec n →ₗ[ZMod 2] ZMod 2,
          (∃ w0 ∈ W, h w0 = 1) ∧
          (∀ a ∈ RH, ∀ x y : XVec n, f x = a → f y = a → h x = h y) := by
        by_cases hRH0 : RH.card = 0
        · have hWgt : 1 < (subFinset W).card := by
            rw [hWcard]; exact Nat.one_lt_pow (Nat.succ_ne_zero d') (by norm_num)
          rcases Finset.one_lt_card.mp hWgt with ⟨v1, hv1, v2, hv2, hv12⟩
          have hv1W : v1 ∈ W := mem_subFinset.mp hv1
          have hv2W : v2 ∈ W := mem_subFinset.mp hv2
          let w0 := v1 - v2
          have hw0W : w0 ∈ W := W.sub_mem hv1W hv2W
          have hw0ne : w0 ≠ 0 := sub_ne_zero.mpr hv12
          have hex_i : ∃ i : Fin n, w0 i ≠ 0 := by
            by_contra hall
            push Not at hall
            exact hw0ne (funext hall)
          rcases hex_i with ⟨i, hi⟩
          have hi1 : w0 i = 1 := by
            rcases zmod2_eq_zero_or_one (w0 i) with h0 | h1
            · exact (hi h0).elim
            · exact h1
          refine ⟨projLM i, ⟨w0, hw0W, hi1⟩, ?_⟩
          intro a ha
          rw [Finset.card_eq_zero.mp hRH0] at ha
          simp at ha
        · by_cases hRH1 : RH.card = 1
          · have hdpos : 0 < d' := by
              by_contra h0
              exact hbase ⟨by omega, hRH1⟩
            rcases Finset.card_eq_one.mp hRH1 with ⟨a, hRHa⟩
            have haRH : a ∈ RH := by rw [hRHa]; simp
            have hfa2 : 1 < (Finset.univ.filter (fun x => f x = a)).card := by rw [h2 a]; omega
            rcases Finset.one_lt_card.mp hfa2 with ⟨u, hu, v, hv, huv⟩
            have hfu : f u = a := (Finset.mem_filter.mp hu).2
            have hfv : f v = a := (Finset.mem_filter.mp hv).2
            have huH : u ∈ H := (Finset.mem_filter.mp haRH).2 u hfu
            have hvH : v ∈ H := (Finset.mem_filter.mp haRH).2 v hfv
            let K : Submodule (ZMod 2) (XVec n) := Submodule.span (ZMod 2) {u - v}
            have hWge4 : 4 ≤ (subFinset W).card := by
              rw [hWcard]
              calc 4 = 2 ^ 2 := by norm_num
                _ ≤ 2 ^ (d' + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
            have hKle2 : (subFinset K).card ≤ 2 :=
              card_span_singleton_le_two (u - v)
            have hex_w : ∃ w0 ∈ W, w0 ∉ K := by
              by_contra hall
              push Not at hall
              have hsub : subFinset W ⊆ subFinset K := by
                intro x hx
                exact mem_subFinset.mpr (hall x (mem_subFinset.mp hx))
              have := Finset.card_le_card hsub
              omega
            rcases hex_w with ⟨w0, hw0W, hw0K⟩
            rcases exists_dual_sep K hw0K with ⟨h, hK0, hw01⟩
            refine ⟨h, ⟨w0, hw0W, hw01⟩, ?_⟩
            intro b hb x y hfx hfy
            rw [hRHa, Finset.mem_singleton] at hb
            rw [hb] at hfx hfy
            have hpair : Finset.univ.filter (fun z => f z = a) = {u, v} := by
              have hsub : ({u, v} : Finset (XVec n)) ⊆ Finset.univ.filter (fun z => f z = a) := by
                intro z hz
                simp only [Finset.mem_insert, Finset.mem_singleton] at hz
                rcases hz with rfl | rfl
                · exact hu
                · exact hv
              exact (Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_pair huv, h2 a])).symm
            have hxuv : x = u ∨ x = v := by
              have : x ∈ ({u, v} : Finset (XVec n)) := hpair ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfx⟩
              simpa using this
            have hyuv : y = u ∨ y = v := by
              have : y ∈ ({u, v} : Finset (XVec n)) := hpair ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfy⟩
              simpa using this
            have huv0 : h (u - v) = 0 := hK0 (u - v) (Submodule.subset_span rfl)
            have hhu : h u = h v := sub_eq_zero.mp (by rwa [map_sub] at huv0)
            rcases hxuv with rfl | rfl <;> rcases hyuv with rfl | rfl <;> simp [hhu]
          · have hRHgt : 1 < RH.card := by omega
            have hRHsub : RH ⊆ R := Finset.filter_subset _ _
            rcases hRsep RH hRHsub hRHgt with ⟨x, y, hfxRH, hfyRH, hnotdir⟩
            let D := Submodule.span (ZMod 2)
              {z : XVec n | ∃ x' y' : XVec n, f x' ∈ RH ∧ f y' = f x' ∧ z = x' - y'}
            rcases exists_dual_sep D hnotdir with ⟨h, hD0, hxy1⟩
            have hxH : x ∈ H := (Finset.mem_filter.mp hfxRH).2 x rfl
            have hyH : y ∈ H := (Finset.mem_filter.mp hfyRH).2 y rfl
            have hxyW : x - y ∈ W := by
              have h1 : x - x0 ∈ W := mem_cosetFinset.mp hxH
              have h2' : y - x0 ∈ W := mem_cosetFinset.mp hyH
              have heq : (x - x0) - (y - x0) = x - y := by abel
              rw [← heq]
              exact W.sub_mem h1 h2'
            refine ⟨h, ⟨x - y, hxyW, hxy1⟩, ?_⟩
            intro a ha x' y' hfx' hfy'
            have hmemD : x' - y' ∈ D :=
              Submodule.subset_span ⟨x', y', by rwa [hfx'], hfy'.trans hfx'.symm, rfl⟩
            have h0 : h (x' - y') = 0 := hD0 (x' - y') hmemD
            exact sub_eq_zero.mp (by rwa [map_sub] at h0)
      rcases hex_h with ⟨h, ⟨w0, hw0W, hw0h⟩, hconst⟩
      let W' : Submodule (ZMod 2) (XVec n) := W ⊓ LinearMap.ker h
      have hW'card : (subFinset W').card = 2 ^ d' := by
        have hhalf := sub_ker_card_half W h hw0W hw0h
        rw [hWcard, pow_succ'] at hhalf
        exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2) hhalf.symm
      let x0_0 : XVec n := if h x0 = 0 then x0 else x0 + w0
      let x0_1 : XVec n := if h x0 = 1 then x0 else x0 + w0
      have hx0_0_H : x0_0 - x0 ∈ W := by
        dsimp only [x0_0]
        split_ifs
        · simp [W.zero_mem]
        · simpa using hw0W
      have hx0_1_H : x0_1 - x0 ∈ W := by
        dsimp only [x0_1]
        split_ifs
        · simp [W.zero_mem]
        · simpa using hw0W
      have hx0_0_h : h x0_0 = 0 := by
        dsimp only [x0_0]
        split_ifs with h0
        · exact h0
        · have h1 : h x0 = 1 := by
            rcases zmod2_eq_zero_or_one (h x0) with hz | ho
            · exact (h0 hz).elim
            · exact ho
          rw [map_add, h1, hw0h]; exact zmod2_add_self 1
      have hx0_1_h : h x0_1 = 1 := by
        dsimp only [x0_1]
        split_ifs with h1
        · exact h1
        · have h0 : h x0 = 0 := by
            rcases zmod2_eq_zero_or_one (h x0) with hz | ho
            · exact hz
            · exact (h1 ho).elim
          rw [map_add, h0, hw0h, zero_add]
      let H0 : Finset (XVec n) := cosetFinset W' x0_0
      let H1 : Finset (XVec n) := cosetFinset W' x0_1
      have hH0_eq : H0 = H.filter (fun x => h x = 0) := by
        ext x
        simp only [H0, H, W', Finset.mem_filter, mem_cosetFinset, Submodule.mem_inf,
          LinearMap.mem_ker, map_sub, hx0_0_h, sub_zero]
        constructor
        · rintro ⟨hxW, hxh⟩
          have heq : x - x0 = (x - x0_0) + (x0_0 - x0) := by abel
          exact ⟨by rw [heq]; exact W.add_mem hxW hx0_0_H, hxh⟩
        · rintro ⟨hxW, hxh⟩
          have heq : x - x0_0 = (x - x0) - (x0_0 - x0) := by abel
          exact ⟨by rw [heq]; exact W.sub_mem hxW hx0_0_H, hxh⟩
      have hH1_eq : H1 = H.filter (fun x => h x = 1) := by
        ext x
        simp only [H1, H, W', Finset.mem_filter, mem_cosetFinset, Submodule.mem_inf,
          LinearMap.mem_ker, map_sub, hx0_1_h, sub_eq_zero]
        constructor
        · rintro ⟨hxW, hxh⟩
          have heq : x - x0 = (x - x0_1) + (x0_1 - x0) := by abel
          exact ⟨by rw [heq]; exact W.add_mem hxW hx0_1_H, hxh⟩
        · rintro ⟨hxW, hxh⟩
          have heq : x - x0_1 = (x - x0) - (x0_1 - x0) := by abel
          exact ⟨by rw [heq]; exact W.sub_mem hxW hx0_1_H, hxh⟩
      have hH_disj : Disjoint H0 H1 := by
        rw [hH0_eq, hH1_eq, Finset.disjoint_left]
        intro x hx0 hx1
        have h0 := (Finset.mem_filter.mp hx0).2
        have h1 := (Finset.mem_filter.mp hx1).2
        rw [h0] at h1
        exact zero_ne_one h1
      have hH_union : H0 ∪ H1 = H := by
        rw [hH0_eq, hH1_eq]
        ext x
        simp only [Finset.mem_union, Finset.mem_filter]
        constructor
        · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
        · intro hx
          rcases zmod2_eq_zero_or_one (h x) with h0 | h1
          · exact Or.inl ⟨hx, h0⟩
          · exact Or.inr ⟨hx, h1⟩
      have hclosed0 : ∀ a ∈ R, (∀ x : XVec n, f x = a → x ∈ H0) ∨ (∀ x : XVec n, f x = a → x ∉ H0) := by
        intro a haR
        rcases hclosed a haR with hin | hout
        · have haRH : a ∈ RH := Finset.mem_filter.mpr ⟨haR, hin⟩
          have hfa_ne : (Finset.univ.filter (fun x => f x = a)).Nonempty :=
            Finset.card_pos.mp (by rw [h2 a]; omega)
          rcases hfa_ne with ⟨xa, hxa⟩
          have hfxa : f xa = a := (Finset.mem_filter.mp hxa).2
          rcases zmod2_eq_zero_or_one (h xa) with h0 | h1
          · left
            intro x hfx
            rw [hH0_eq, Finset.mem_filter]
            exact ⟨hin x hfx, (hconst a haRH x xa hfx hfxa).trans h0⟩
          · right
            intro x hfx hx0
            rw [hH0_eq, Finset.mem_filter] at hx0
            have := (hconst a haRH x xa hfx hfxa).trans h1
            rw [hx0.2] at this
            exact zero_ne_one this
        · right
          intro x hfx hx0
          rw [hH0_eq, Finset.mem_filter] at hx0
          exact hout x hfx hx0.1
      have hclosed1 : ∀ a ∈ R, (∀ x : XVec n, f x = a → x ∈ H1) ∨ (∀ x : XVec n, f x = a → x ∉ H1) := by
        intro a haR
        rcases hclosed a haR with hin | hout
        · have haRH : a ∈ RH := Finset.mem_filter.mpr ⟨haR, hin⟩
          have hfa_ne : (Finset.univ.filter (fun x => f x = a)).Nonempty :=
            Finset.card_pos.mp (by rw [h2 a]; omega)
          rcases hfa_ne with ⟨xa, hxa⟩
          have hfxa : f xa = a := (Finset.mem_filter.mp hxa).2
          rcases zmod2_eq_zero_or_one (h xa) with h0 | h1
          · right
            intro x hfx hx1
            rw [hH1_eq, Finset.mem_filter] at hx1
            have := (hconst a haRH x xa hfx hfxa).trans h0
            rw [hx1.2] at this
            exact one_ne_zero this
          · left
            intro x hfx
            rw [hH1_eq, Finset.mem_filter]
            exact ⟨hin x hfx, (hconst a haRH x xa hfx hfxa).trans h1⟩
        · right
          intro x hfx hx1
          rw [hH1_eq, Finset.mem_filter] at hx1
          exact hout x hfx hx1.1
      let RH0 : Finset (Fin m) := R.filter (fun a => ∀ x : XVec n, f x = a → x ∈ H0)
      let RH1 : Finset (Fin m) := R.filter (fun a => ∀ x : XVec n, f x = a → x ∈ H1)
      have hRH_disj : Disjoint RH0 RH1 := by
        rw [Finset.disjoint_left]
        intro a ha0 ha1
        have hfa_ne : (Finset.univ.filter (fun x => f x = a)).Nonempty :=
          Finset.card_pos.mp (by rw [h2 a]; omega)
        rcases hfa_ne with ⟨xa, hxa⟩
        have hfxa : f xa = a := (Finset.mem_filter.mp hxa).2
        exact Finset.disjoint_left.mp hH_disj
          ((Finset.mem_filter.mp ha0).2 xa hfxa) ((Finset.mem_filter.mp ha1).2 xa hfxa)
      have hRH_union : RH0 ∪ RH1 = RH := by
        ext a
        simp only [RH0, RH1, RH, Finset.mem_union, Finset.mem_filter]
        constructor
        · rintro (⟨haR, h0⟩ | ⟨haR, h1⟩)
          · exact ⟨haR, fun x hfx => hH_union ▸ Finset.mem_union_left H1 (h0 x hfx)⟩
          · exact ⟨haR, fun x hfx => hH_union ▸ Finset.mem_union_right H0 (h1 x hfx)⟩
        · rintro ⟨haR, hin⟩
          have hfa_ne : (Finset.univ.filter (fun x => f x = a)).Nonempty :=
            Finset.card_pos.mp (by rw [h2 a]; omega)
          rcases hfa_ne with ⟨xa, hxa⟩
          have hfxa : f xa = a := (Finset.mem_filter.mp hxa).2
          have hxaH : xa ∈ H := hin xa hfxa
          rw [← hH_union, Finset.mem_union] at hxaH
          rcases hxaH with hxa0 | hxa1
          · rcases hclosed0 a haR with h0 | hnot0
            · exact Or.inl ⟨haR, h0⟩
            · exact (hnot0 xa hfxa hxa0).elim
          · rcases hclosed1 a haR with h1 | hnot1
            · exact Or.inr ⟨haR, h1⟩
            · exact (hnot1 xa hfxa hxa1).elim
      rcases ih W' x0_0 hW'card hclosed0 with ⟨t0, ht0eval, ht0card, ht0cost⟩
      rcases ih W' x0_1 hW'card hclosed1 with ⟨t1, ht1eval, ht1card, ht1cost⟩
      let t : ATree n m := ATree.node h 1 t0 t1
      refine ⟨t, ?_, ?_, ?_⟩
      · intro x hx
        dsimp only [t, ATree.eval]
        by_cases hh1 : h x = 1
        · simp only [hh1, decide_true, ↓reduceIte]
          exact ht1eval x (by change x ∈ H1; rw [hH1_eq]; exact Finset.mem_filter.mpr ⟨hx, hh1⟩)
        · simp only [hh1, decide_false, Bool.false_eq_true, ↓reduceIte]
          have hh0 : h x = 0 := by
            rcases zmod2_eq_zero_or_one (h x) with h0 | h1
            · exact h0
            · exact (hh1 h1).elim
          exact ht0eval x (by change x ∈ H0; rw [hH0_eq]; exact Finset.mem_filter.mpr ⟨hx, hh0⟩)
      · have hleaves : t.leaves.card = t0.leaves.card + t1.leaves.card :=
          ATree.leaves_card_node h 1 t0 t1
        have hRHcard : RH.card = RH0.card + RH1.card := by
          rw [← hRH_union, Finset.card_union_of_disjoint hRH_disj]
        change t0.leaves.card + RH0.card = 2 ^ d' at ht0card
        change t1.leaves.card + RH1.card = 2 ^ d' at ht1card
        rw [hleaves, hRHcard, pow_succ']
        omega
      · have hdisj_leaves : Disjoint (t0.leaves.image (false :: ·)) (t1.leaves.image (true :: ·)) := by
          rw [Finset.disjoint_left]
          intro p hp0 hp1
          rcases Finset.mem_image.mp hp0 with ⟨q0, _, h0⟩
          rcases Finset.mem_image.mp hp1 with ⟨q1, _, h1⟩
          have h01 := h0.trans h1.symm
          injection h01 with hb _
          exact Bool.false_ne_true hb
        have hcost_split : t.leaves.sum (fun p => p.length * (H.filter (fun x => Reaches t.query p x)).sum mass) =
            (t0.leaves.sum (fun q => (q.length + 1) * (H0.filter (fun x => Reaches t0.query q x)).sum mass)) +
            (t1.leaves.sum (fun q => (q.length + 1) * (H1.filter (fun x => Reaches t1.query q x)).sum mass)) := by
          change ((t0.leaves.image (false :: ·)) ∪ (t1.leaves.image (true :: ·))).sum
            (fun p => p.length * (H.filter (fun x => Reaches t.query p x)).sum mass) = _
          rw [Finset.sum_union hdisj_leaves, Finset.sum_image, Finset.sum_image]
          · congr 1
            · refine Finset.sum_congr rfl (fun q _ => ?_)
              simp only [List.length_cons]
              congr 1
              have hfilt : H.filter (fun x => Reaches t.query (false :: q) x) =
                  H0.filter (fun x => Reaches t0.query q x) := by
                ext x
                dsimp only [t]
                simp only [Finset.mem_filter, hH0_eq, ATree.reaches_node_false]
                constructor
                · rintro ⟨hxH, hne1, hrq⟩
                  have hh0 : h x = 0 := by
                    rcases zmod2_eq_zero_or_one (h x) with h0 | h1
                    · exact h0
                    · exact (hne1 h1).elim
                  exact ⟨⟨hxH, hh0⟩, hrq⟩
                · rintro ⟨⟨hxH, hh0⟩, hrq⟩
                  exact ⟨hxH, by rw [hh0]; exact zero_ne_one, hrq⟩
              rw [hfilt]
            · refine Finset.sum_congr rfl (fun q _ => ?_)
              simp only [List.length_cons]
              congr 1
              have hfilt : H.filter (fun x => Reaches t.query (true :: q) x) =
                  H1.filter (fun x => Reaches t1.query q x) := by
                ext x
                dsimp only [t]
                simp only [Finset.mem_filter, hH1_eq, ATree.reaches_node_true]
                tauto
              rw [hfilt]
          · intro q1 _ q2 _ heq; injection heq
          · intro q1 _ q2 _ heq; injection heq
        have hcost0 : t0.leaves.sum (fun q => (q.length + 1) * (H0.filter (fun x => Reaches t0.query q x)).sum mass) =
            t0.leaves.sum (fun q => q.length * (H0.filter (fun x => Reaches t0.query q x)).sum mass) + H0.sum mass := by
          have hexp : ∀ q ∈ t0.leaves,
              (q.length + 1) * (H0.filter (fun x => Reaches t0.query q x)).sum mass =
              q.length * (H0.filter (fun x => Reaches t0.query q x)).sum mass +
              (H0.filter (fun x => Reaches t0.query q x)).sum mass := fun q _ => by ring
          rw [Finset.sum_congr rfl hexp, Finset.sum_add_distrib, ATree.sum_leaves_mass t0 H0 mass]
        have hcost1 : t1.leaves.sum (fun q => (q.length + 1) * (H1.filter (fun x => Reaches t1.query q x)).sum mass) =
            t1.leaves.sum (fun q => q.length * (H1.filter (fun x => Reaches t1.query q x)).sum mass) + H1.sum mass := by
          have hexp : ∀ q ∈ t1.leaves,
              (q.length + 1) * (H1.filter (fun x => Reaches t1.query q x)).sum mass =
              q.length * (H1.filter (fun x => Reaches t1.query q x)).sum mass +
              (H1.filter (fun x => Reaches t1.query q x)).sum mass := fun q _ => by ring
          rw [Finset.sum_congr rfl hexp, Finset.sum_add_distrib, ATree.sum_leaves_mass t1 H1 mass]
        have hRmass_split : (H.filter (fun x => f x ∈ RH)).sum mass =
            (H0.filter (fun x => f x ∈ RH0)).sum mass + (H1.filter (fun x => f x ∈ RH1)).sum mass := by
          have hdisjR : Disjoint (H0.filter (fun x => f x ∈ RH0)) (H1.filter (fun x => f x ∈ RH1)) := by
            rw [Finset.disjoint_left]
            intro x hx0 hx1
            exact Finset.disjoint_left.mp hH_disj (Finset.mem_filter.mp hx0).1 (Finset.mem_filter.mp hx1).1
          have hunionR : (H0.filter (fun x => f x ∈ RH0)) ∪ (H1.filter (fun x => f x ∈ RH1)) =
              H.filter (fun x => f x ∈ RH) := by
            ext x
            simp only [Finset.mem_union, Finset.mem_filter]
            constructor
            · rintro (⟨hx0, hfx0⟩ | ⟨hx1, hfx1⟩)
              · exact ⟨hH_union ▸ Finset.mem_union_left H1 hx0, hRH_union ▸ Finset.mem_union_left RH1 hfx0⟩
              · exact ⟨hH_union ▸ Finset.mem_union_right H0 hx1, hRH_union ▸ Finset.mem_union_right RH0 hfx1⟩
            · rintro ⟨hxH, hfxRH⟩
              rw [← hRH_union, Finset.mem_union] at hfxRH
              rcases hfxRH with h0 | h1
              · exact Or.inl ⟨(Finset.mem_filter.mp h0).2 x rfl, h0⟩
              · exact Or.inr ⟨(Finset.mem_filter.mp h1).2 x rfl, h1⟩
          rw [← hunionR, Finset.sum_union hdisjR]
        have hHmass_split : H.sum mass = H0.sum mass + H1.sum mass := by
          rw [← hH_union, Finset.sum_union hH_disj]
        rw [hcost_split, hcost0, hcost1, hRmass_split, hHmass_split]
        change t0.leaves.sum (fun p => p.length * (H0.filter (fun x => Reaches t0.query p x)).sum mass) +
          (H0.filter (fun x => f x ∈ RH0)).sum mass = d' * H0.sum mass at ht0cost
        change t1.leaves.sum (fun p => p.length * (H1.filter (fun x => Reaches t1.query p x)).sum mass) +
          (H1.filter (fun x => f x ∈ RH1)).sum mass = d' * H1.sum mass at ht1cost
        linarith

end PEqualNP.Outside.L_pcx_358_aux

theorem PEqualNP.Outside.L_pcx_358 :
∀ (n m : ℕ),
  let X := Fin n → ZMod 2
  let shape := fun (N J : Finset (List Bool)) =>
    [] ∈ N ∧ J ⊆ N ∧
    (∀ (p : List Bool) (b : Bool), p ++ [b] ∈ N → p ∈ J) ∧
    ∀ p ∈ J, p ++ [false] ∈ N ∧ p ++ [true] ∈ N
  let queries := fun (V : Type) [AddCommGroup V] [Module (ZMod 2) V] =>
    {f : V → Bool | ∃ (l : V →ₗ[ZMod 2] ZMod 2) (b : ZMod 2), f = fun x => decide (l x = b)}
  let cert := fun {V O : Type} (qs : Set (V → Bool)) (ok : V → O → Prop)
      (N J : Finset (List Bool)) (q : List Bool → V → Bool) (out : List Bool → O) =>
    shape N J ∧ (∀ p ∈ J, q p ∈ qs) ∧ ∀ p ∈ N \ J, ∀ x : V,
      (∀ j : Fin p.length, q (p.take j.val) x = p.get j) → ok x (out p)
  ∀ (f : X → Fin m), (∀ a, (Finset.univ.filter (fun x => f x = a)).card = 2) →
    ∀ (mass : X → ℕ) (K B : ℕ),
    (∃ (N J : Finset (List Bool)) (q : List Bool → X → Bool) (out : List Bool → Fin m),
      cert (queries X) (fun x a => f x = a) N J q out ∧ (N \ J).card ≤ K ∧
      (N \ J).sum (fun p => p.length * (Finset.univ.filter (fun x : X =>
        ∀ j : Fin p.length, q (p.take j.val) x = p.get j)).sum mass) ≤ B) ↔
    ∃ R : Finset (Fin m),
      (∀ S ⊆ R, 1 < S.card →
        let directions := Submodule.span (ZMod 2)
          {z : X | ∃ x y : X, f x ∈ S ∧ f y = f x ∧ z = x-y}
        ∃ x y : X, f x ∈ S ∧ f y ∈ S ∧ x-y ∉ directions) ∧
      2^n ≤ K + R.card ∧
      n * Finset.univ.sum mass ≤ B + (Finset.univ.filter (fun x : X => f x ∈ R)).sum mass := by
  intro n m
  dsimp only
  intro f h2 mass K B
  constructor
  · rintro ⟨N, J, q, out, ⟨hS, hq, hok⟩, hK, hB⟩
    exact PEqualNP.Outside.L_pcx_358_aux.forward_dir f h2 mass K B N J q out hS hq hok hK hB
  · rintro ⟨R, hRsep, hK, hB⟩
    have hWtop : (PEqualNP.Outside.L_pcx_358_aux.subFinset (⊤ : Submodule (ZMod 2) (Fin n → ZMod 2))).card = 2 ^ n := by
      have heq : PEqualNP.Outside.L_pcx_358_aux.subFinset (⊤ : Submodule (ZMod 2) (Fin n → ZMod 2)) = Finset.univ := by
        ext v; simp [PEqualNP.Outside.L_pcx_358_aux.mem_subFinset]
      rw [heq]
      exact PEqualNP.Outside.L_pcx_358_aux.card_xvec n
    have hclosed : ∀ a ∈ R,
        (∀ x : Fin n → ZMod 2, f x = a → x ∈ PEqualNP.Outside.L_pcx_358_aux.cosetFinset (⊤ : Submodule (ZMod 2) (Fin n → ZMod 2)) 0) ∨
        (∀ x : Fin n → ZMod 2, f x = a → x ∉ PEqualNP.Outside.L_pcx_358_aux.cosetFinset (⊤ : Submodule (ZMod 2) (Fin n → ZMod 2)) 0) := by
      intro a _
      left
      intro x _; simp [PEqualNP.Outside.L_pcx_358_aux.mem_cosetFinset]
    rcases PEqualNP.Outside.L_pcx_358_aux.build_pair_tree f h2 mass R hRsep n ⊤ 0 hWtop hclosed with
      ⟨t, hteval, htcard, htcost⟩
    have hHun : PEqualNP.Outside.L_pcx_358_aux.cosetFinset (⊤ : Submodule (ZMod 2) (Fin n → ZMod 2)) 0 = Finset.univ := by
      ext x; simp [PEqualNP.Outside.L_pcx_358_aux.mem_cosetFinset]
    have hRH : R.filter (fun a => ∀ x : Fin n → ZMod 2, f x = a → x ∈ PEqualNP.Outside.L_pcx_358_aux.cosetFinset (⊤ : Submodule (ZMod 2) (Fin n → ZMod 2)) 0) = R := by
      ext a; simp [PEqualNP.Outside.L_pcx_358_aux.mem_cosetFinset]
    rw [hRH] at htcard htcost
    rw [hHun] at htcost
    refine ⟨t.nodes, t.internal, t.query, t.out, ⟨t.shape_ok, t.queries_ok, ?_⟩, ?_, ?_⟩
    · intro p hp x hrx
      rw [t.nodes_sdiff_internal] at hp
      rw [t.reaches_out p hp x hrx]
      exact (hteval x (by simp [PEqualNP.Outside.L_pcx_358_aux.mem_cosetFinset])).symm
    · rw [t.nodes_sdiff_internal]
      omega
    · rw [t.nodes_sdiff_internal]
      have hcost_eq :
          t.leaves.sum (fun p => p.length * (Finset.univ.filter (fun x : Fin n → ZMod 2 =>
            ∀ j : Fin p.length, t.query (p.take j.val) x = p.get j)).sum mass) =
          t.leaves.sum (fun p => p.length * (Finset.univ.filter (fun x : PEqualNP.Outside.L_pcx_358_aux.XVec n =>
            PEqualNP.Outside.L_pcx_358_aux.Reaches t.query p x)).sum mass) := rfl
      have hmass_eq :
          (Finset.univ.filter (fun x : Fin n → ZMod 2 => f x ∈ R)).sum mass =
          (Finset.univ.filter (fun x : PEqualNP.Outside.L_pcx_358_aux.XVec n => f x ∈ R)).sum mass := rfl
      rw [hcost_eq]
      rw [hmass_eq] at hB
      omega
