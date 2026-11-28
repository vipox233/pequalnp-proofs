import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_30664_aux

section duality

variable {α : Type} [Fintype α] [DecidableEq α]

def IsM (M : Finset (Finset α)) : Prop :=
  (∀ e ∈ M, e.card = 2) ∧ (∀ e ∈ M, ∀ g ∈ M, e ≠ g → Disjoint e g)

theorem IsM.mono {M N : Finset (Finset α)} (h : IsM M) (hs : N ⊆ M) : IsM N :=
  ⟨fun e he => h.1 e (hs he), fun e he g hg => h.2 e (hs he) g (hs hg)⟩

theorem isM_empty : IsM (∅ : Finset (Finset α)) := ⟨by simp, by simp⟩

noncomputable def matchings : Finset (Finset (Finset α)) := by
  classical exact Finset.univ.filter IsM

theorem mem_matchings (M : Finset (Finset α)) : M ∈ matchings ↔ IsM M := by
  classical
  simp [matchings]

noncomputable def nu (w : Finset α → ℕ) : ℕ := matchings.sup (fun M => ∑ e ∈ M, w e)

theorem le_nu (w : Finset α → ℕ) {M : Finset (Finset α)} (h : IsM M) : ∑ e ∈ M, w e ≤ nu w :=
  Finset.le_sup (f := fun M => ∑ e ∈ M, w e) ((mem_matchings M).2 h)

theorem nu_le (w : Finset α → ℕ) (c : ℕ) (h : ∀ M, IsM M → ∑ e ∈ M, w e ≤ c) : nu w ≤ c :=
  Finset.sup_le fun M hM => h M ((mem_matchings M).1 hM)

theorem exists_nu (w : Finset α → ℕ) : ∃ M, IsM M ∧ ∑ e ∈ M, w e = nu w := by
  obtain ⟨M, hM, h⟩ := Finset.exists_mem_eq_sup (matchings (α := α))
    ⟨∅, (mem_matchings _).2 isM_empty⟩ (fun M => ∑ e ∈ M, w e)
  exact ⟨M, (mem_matchings M).1 hM, h.symm⟩

def Dual (w : Finset α → ℕ) (y : α → ℕ) (z : Finset α → ℕ) : Prop :=
  (∀ U, z U ≠ 0 → U.card % 2 = 1) ∧
  ∀ e : Finset α, e.card = 2 → w e ≤ ∑ v ∈ e, y v + ∑ U ∈ Finset.univ.filter (fun T => e ⊆ T), z U

def cost (y : α → ℕ) (z : Finset α → ℕ) : ℕ := ∑ v, y v + ∑ U : Finset α, (U.card / 2) * z U

theorem matched_card (M : Finset (Finset α)) (h : IsM M) : (M.biUnion id).card = 2 * M.card := by
  rw [Finset.card_biUnion]
  · rw [Finset.sum_congr rfl (fun e he => (show (id e).card = 2 from h.1 e he))]
    simp [mul_comm]
  · intro a ha b hb hab
    exact h.2 a ha b hb hab

def Adj (E : Finset (Finset α)) (a b : α) : Prop := a ≠ b ∧ ({a, b} : Finset α) ∈ E

def Reach (E : Finset (Finset α)) : ℕ → α → α → Prop
  | 0, a, b => a = b
  | n + 1, a, b => ∃ c, Adj E a c ∧ Reach E n c b

theorem adj_symm {E : Finset (Finset α)} {a b : α} (h : Adj E a b) : Adj E b a :=
  ⟨h.1.symm, by rw [Finset.pair_comm]; exact h.2⟩

theorem reach_snoc {E : Finset (Finset α)} {n : ℕ} {a b c : α} (h : Reach E n a b) (hb : Adj E b c) :
    Reach E (n + 1) a c := by
  induction n generalizing a with
  | zero =>
    have h' : a = b := h
    subst h'
    exact ⟨c, hb, rfl⟩
  | succ n ih =>
    obtain ⟨d, had, hd⟩ := h
    exact ⟨d, had, ih hd⟩

theorem reach_symm {E : Finset (Finset α)} {n : ℕ} {a b : α} (h : Reach E n a b) : Reach E n b a := by
  induction n generalizing a with
  | zero => exact (show a = b from h).symm
  | succ n ih =>
    obtain ⟨d, had, hd⟩ := h
    exact reach_snoc (ih hd) (adj_symm had)

theorem reach_trans {E : Finset (Finset α)} {n m : ℕ} {a b c : α} (h : Reach E n a b)
    (h' : Reach E m b c) : ∃ l, Reach E l a c := by
  induction n generalizing a with
  | zero => exact ⟨m, (show a = b from h) ▸ h'⟩
  | succ n ih =>
    obtain ⟨d, had, hd⟩ := h
    obtain ⟨l, hl⟩ := ih hd
    exact ⟨l + 1, d, had, hl⟩

noncomputable def comp (E : Finset (Finset α)) (t : α) : Finset α := by
  classical exact Finset.univ.filter (fun v => ∃ n, Reach E n t v)

theorem mem_comp (E : Finset (Finset α)) (t v : α) : v ∈ comp E t ↔ ∃ n, Reach E n t v := by
  classical
  simp [comp]

theorem self_comp (E : Finset (Finset α)) (t : α) : t ∈ comp E t :=
  (mem_comp E t t).2 ⟨0, rfl⟩

theorem comp_closed {E : Finset (Finset α)} (hE : ∀ e ∈ E, e.card = 2) (t : α) {e : Finset α}
    (he : e ∈ E) {v : α} (hv : v ∈ e) (hc : v ∈ comp E t) : e ⊆ comp E t := by
  intro u hu
  by_cases huv : u = v
  · exact huv ▸ hc
  · have : e = {v, u} := by
      symm
      apply Finset.eq_of_subset_of_card_le
      · intro a ha
        simp only [Finset.mem_insert, Finset.mem_singleton] at ha
        rcases ha with rfl | rfl <;> assumption
      · rw [hE e he, Finset.card_pair (Ne.symm huv)]
    obtain ⟨n, hn⟩ := (mem_comp E t v).1 hc
    exact (mem_comp E t u).2 ⟨n + 1, reach_snoc hn ⟨Ne.symm huv, this ▸ he⟩⟩

theorem comp_connected (E : Finset (Finset α)) (hE : ∀ e ∈ E, e.card = 2) (t : α) :
    (comp E t).card ≤ (E.filter (fun e => e ⊆ comp E t)).card + 1 := by
  classical
  let good := (comp E t).powerset.filter
    (fun S => t ∈ S ∧ S.card ≤ (E.filter (fun e => e ⊆ S)).card + 1)
  have hne : good.Nonempty := by
    refine ⟨{t}, Finset.mem_filter.2 ⟨Finset.mem_powerset.2 ?_, by simp, by simp⟩⟩
    simpa using self_comp E t
  obtain ⟨S, hS, hmax⟩ := Finset.exists_max_image good Finset.card hne
  obtain ⟨hSsub, htS, hScard⟩ := Finset.mem_filter.1 hS
  rw [Finset.mem_powerset] at hSsub
  have hclosed : ∀ a b, a ∈ S → Adj E a b → b ∈ S := by
    intro a b ha hab
    by_contra hb
    have hbc : b ∈ comp E t := by
      obtain ⟨n, hn⟩ := (mem_comp E t a).1 (hSsub ha)
      exact (mem_comp E t b).2 ⟨n + 1, reach_snoc hn hab⟩
    have hmem : insert b S ∈ good := by
      refine Finset.mem_filter.2 ⟨Finset.mem_powerset.2 ?_, Finset.mem_insert_of_mem htS, ?_⟩
      · exact Finset.insert_subset hbc hSsub
      · have hlt : (E.filter (fun e => e ⊆ S)).card < (E.filter (fun e => e ⊆ insert b S)).card := by
          apply Finset.card_lt_card
          refine (Finset.ssubset_iff_of_subset ?_).2 ⟨{a, b}, ?_, ?_⟩
          · intro e he
            rw [Finset.mem_filter] at he ⊢
            exact ⟨he.1, he.2.trans (Finset.subset_insert _ _)⟩
          · rw [Finset.mem_filter]
            refine ⟨hab.2, ?_⟩
            intro u hu
            simp only [Finset.mem_insert, Finset.mem_singleton] at hu
            rcases hu with rfl | rfl
            · exact Finset.mem_insert_of_mem ha
            · exact Finset.mem_insert_self _ _
          · rw [Finset.mem_filter]
            intro h
            exact hb (h.2 (by simp))
        rw [Finset.card_insert_of_notMem hb]
        omega
    have := hmax _ hmem
    rw [Finset.card_insert_of_notMem hb] at this
    omega
  have hall : ∀ n a b, Reach E n a b → a ∈ S → b ∈ S := by
    intro n
    induction n with
    | zero => intro a b h ha; exact (show a = b from h) ▸ ha
    | succ n ih =>
      intro a b h ha
      obtain ⟨c, hac, hc⟩ := h
      exact ih c b hc (hclosed a c ha hac)
  have hEq : comp E t = S := by
    apply Finset.Subset.antisymm _ hSsub
    intro v hv
    obtain ⟨n, hn⟩ := (mem_comp E t v).1 hv
    exact hall n t v hn htS
  rw [hEq]
  exact hScard

noncomputable def posE (w : Finset α → ℕ) : Finset (Finset α) :=
  Finset.univ.filter (fun e => e.card = 2 ∧ 0 < w e)

theorem mem_posE (w : Finset α → ℕ) (e : Finset α) : e ∈ posE w ↔ e.card = 2 ∧ 0 < w e := by
  simp [posE]

theorem isM_swap (M N : Finset (Finset α)) (hM : IsM M) (hN : IsM N) (R : Finset α)
    (hMR : ∀ e ∈ M, ∀ v ∈ e, v ∈ R → e ⊆ R) (hNR : ∀ e ∈ N, ∀ v ∈ e, v ∈ R → e ⊆ R) :
    IsM (M.filter (fun e => ¬ e ⊆ R) ∪ N.filter (fun e => e ⊆ R)) := by
  constructor
  · intro e he
    rcases Finset.mem_union.1 he with h | h
    · exact hM.1 e (Finset.mem_filter.1 h).1
    · exact hN.1 e (Finset.mem_filter.1 h).1
  · intro e he g hg hne
    rcases Finset.mem_union.1 he with h | h <;> rcases Finset.mem_union.1 hg with h' | h' <;>
      rw [Finset.mem_filter] at h h'
    · exact hM.2 e h.1 g h'.1 hne
    · rw [Finset.disjoint_left]
      intro v hv hv'
      exact h.2 (hMR e h.1 v hv (h'.2 hv'))
    · rw [Finset.disjoint_left]
      intro v hv hv'
      exact h'.2 (hMR g h'.1 v hv' (h.2 hv))
    · exact hN.2 e h.1 g h'.1 hne

theorem sum_swap (M N : Finset (Finset α)) (hM : IsM M) (hN : IsM N) (R : Finset α)
    (hMR : ∀ e ∈ M, ∀ v ∈ e, v ∈ R → e ⊆ R) (f : Finset α → ℕ) :
    ∑ e ∈ M.filter (fun e => ¬ e ⊆ R) ∪ N.filter (fun e => e ⊆ R), f e =
      ∑ e ∈ M.filter (fun e => ¬ e ⊆ R), f e + ∑ e ∈ N.filter (fun e => e ⊆ R), f e := by
  apply Finset.sum_union
  rw [Finset.disjoint_left]
  intro e he he'
  rw [Finset.mem_filter] at he he'
  exact he.2 he'.2

theorem cm_core (w w' : Finset α → ℕ) (C : Finset α) (chi : Finset α → ℕ)
    (hC : ∃ p, C = comp (posE w) p)
    (hchi : ∀ e, chi e = if e ⊆ C ∧ e ∈ posE w then 1 else 0)
    (hw : ∀ e, w e = w' e + chi e)
    (hmiss : ∀ v : α, ∃ N, IsM N ∧ (∑ e ∈ N, w e = nu w) ∧ ∀ e ∈ N, e ∈ posE w ∧ v ∉ e) :
    nu w' + C.card / 2 ≤ nu w ∧ C.card % 2 = 1 := by
  classical
  obtain ⟨p, hp⟩ := hC
  have hEc : ∀ e ∈ posE w, e.card = 2 := fun e he => ((mem_posE w e).1 he).1
  have hclosed : ∀ e ∈ posE w, ∀ v ∈ e, v ∈ C → e ⊆ C := by
    intro e he v hv hvC
    rw [hp] at hvC ⊢
    exact comp_closed hEc p he hv hvC
  have hsum : ∀ M : Finset (Finset α), ∑ e ∈ M, w e = ∑ e ∈ M, w' e + ∑ e ∈ M, chi e := by
    intro M
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun e _ => hw e
  have hchiM : ∀ M : Finset (Finset α), ∑ e ∈ M, chi e = (M.filter (fun e => e ⊆ C ∧ e ∈ posE w)).card := by
    intro M
    rw [Finset.card_filter]
    exact Finset.sum_congr rfl fun e _ => hchi e
  have hhalf : ∀ M : Finset (Finset α), IsM M → 2 * (∑ e ∈ M, chi e) ≤ C.card := by
    intro M hM
    rw [hchiM, ← matched_card _ (hM.mono (Finset.filter_subset _ _))]
    apply Finset.card_le_card
    intro v hv
    rw [Finset.mem_biUnion] at hv
    obtain ⟨e, he, hve⟩ := hv
    exact (Finset.mem_filter.1 he).2.1 hve
  let Good : Finset (Finset (Finset α)) := matchings.filter
    (fun M => (∀ e ∈ M, e ∈ posE w) ∧ ∑ e ∈ M, w' e = nu w')
  have hstrip : ∀ M : Finset (Finset α), IsM M → ∃ M', IsM M' ∧ (∀ e ∈ M', e ∈ posE w ∧ e ∈ M) ∧
      ∑ e ∈ M', w e = ∑ e ∈ M, w e ∧ ∑ e ∈ M', w' e = ∑ e ∈ M, w' e := by
    intro M hM
    have h0 : ∀ e ∈ M, e ∉ posE w → w e = 0 := by
      intro e he h
      rw [mem_posE] at h
      have := hM.1 e he
      omega
    refine ⟨M.filter (fun e => e ∈ posE w), hM.mono (Finset.filter_subset _ _), ?_, ?_, ?_⟩
    · intro e he
      rw [Finset.mem_filter] at he
      exact ⟨he.2, he.1⟩
    · apply Finset.sum_filter_of_ne
      intro e he hne
      by_contra h
      exact hne (h0 e he h)
    · apply Finset.sum_filter_of_ne
      intro e he hne
      by_contra h
      have := h0 e he h
      have := hw e
      omega
  have hGne : Good.Nonempty := by
    obtain ⟨M, hM, h⟩ := exists_nu w'
    obtain ⟨M', hM', hp', _, h'⟩ := hstrip M hM
    exact ⟨M', Finset.mem_filter.2 ⟨(mem_matchings _).2 hM', fun e he => (hp' e he).1, h'.trans h⟩⟩
  obtain ⟨M0, hM0, hmax⟩ := Finset.exists_max_image Good (fun M => ∑ e ∈ M, chi e) hGne
  let Bad : ℕ → Prop := fun d => ∃ M ∈ Good, (∑ e ∈ M, chi e = ∑ e ∈ M0, chi e) ∧
    ∃ u v, u ∈ C ∧ v ∈ C ∧ u ≠ v ∧ (∀ e ∈ M, u ∉ e) ∧ (∀ e ∈ M, v ∉ e) ∧ Reach (posE w) d u v
  have hnobad : ∀ d, ¬ Bad d := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      rintro ⟨M, hMG, hMc, u, v, hu, hv, huv, hMu, hMv, hr⟩
      obtain ⟨hMm, hMpos, hMw⟩ := Finset.mem_filter.1 hMG
      rw [mem_matchings] at hMm
      cases d with
      | zero => exact huv hr
      | succ m =>
        obtain ⟨t, hut, htv⟩ := hr
        have htC : t ∈ C := hclosed _ hut.2 u (by simp) hu (by simp)
        have hext : m = 0 → False := by
          intro hm
          subst hm
          have : t = v := htv
          subst this
          have hin : IsM (insert ({u, t} : Finset α) M) := by
            refine ⟨?_, ?_⟩
            · intro e he
              rcases Finset.mem_insert.1 he with rfl | he
              · exact Finset.card_pair huv
              · exact hMm.1 e he
            · intro e he g hg hne
              have key : ∀ g1 ∈ M, Disjoint ({u, t} : Finset α) g1 := by
                intro g1 hg1
                rw [Finset.disjoint_left]
                intro a ha hag
                have h1 := hMu g1 hg1
                have h2 := hMv g1 hg1
                simp only [Finset.mem_insert, Finset.mem_singleton] at ha
                rcases ha with rfl | rfl
                · exact h1 hag
                · exact h2 hag
              rcases Finset.mem_insert.1 he with rfl | he'
              · rcases Finset.mem_insert.1 hg with rfl | hg'
                · exact absurd rfl hne
                · exact key g hg'
              · rcases Finset.mem_insert.1 hg with rfl | hg'
                · exact (key e he').symm
                · exact hMm.2 e he' g hg' hne
          have hnm : ({u, t} : Finset α) ∉ M := fun h => hMu _ h (by simp)
          have h1 := le_nu w' hin
          rw [Finset.sum_insert hnm] at h1
          have hch : chi {u, t} = 1 := by
            rw [hchi, if_pos]
            exact ⟨hclosed _ hut.2 u (by simp) hu, hut.2⟩
          have hmem : insert ({u, t} : Finset α) M ∈ Good := by
            refine Finset.mem_filter.2 ⟨(mem_matchings _).2 hin, ?_, ?_⟩
            · intro e he
              rcases Finset.mem_insert.1 he with rfl | he
              · exact hut.2
              · exact hMpos e he
            · rw [Finset.sum_insert hnm]
              omega
          have h2 : ∑ e ∈ insert ({u, t} : Finset α) M, chi e ≤ ∑ e ∈ M0, chi e := hmax _ hmem
          rw [Finset.sum_insert hnm, hch, hMc] at h2
          omega
        have hm0 : m ≠ 0 := fun h => hext h
        have htv' : t ≠ v := by
          intro h
          subst h
          exact ih 1 (by omega) ⟨M, hMG, hMc, u, t, hu, hv, huv, hMu, hMv, ⟨t, hut, rfl⟩⟩
        have htcov : ¬ ∀ e ∈ M, t ∉ e := by
          intro h
          exact ih 1 (by omega) ⟨M, hMG, hMc, u, t, hu, htC, hut.1, hMu, h, ⟨t, hut, rfl⟩⟩
        obtain ⟨N0, hN0, hN0w, hN0p⟩ := hmiss t
        have hNpos : ∀ e ∈ N0, e ∈ posE w := fun e he => (hN0p e he).1
        have hNt : ∀ e ∈ N0, t ∉ e := fun e he => (hN0p e he).2
        let E := M ∪ N0
        have hEpos : ∀ e ∈ E, e ∈ posE w := by
          intro e he
          rcases Finset.mem_union.1 he with h | h
          · exact hMpos e h
          · exact hNpos e h
        have hE2 : ∀ e ∈ E, e.card = 2 := fun e he => hEc e (hEpos e he)
        let R := comp E t
        have hRC : R ⊆ C := by
          have : ∀ n a b, Reach E n a b → a ∈ C → b ∈ C := by
            intro n
            induction n with
            | zero => intro a b h ha; exact (show a = b from h) ▸ ha
            | succ n ihn =>
              intro a b h ha
              obtain ⟨c, hac, hc⟩ := h
              exact ihn c b hc (hclosed _ (hEpos _ hac.2) a (by simp) ha (by simp))
          intro a ha
          obtain ⟨n, hn⟩ := (mem_comp E t a).1 ha
          exact this n t a hn htC
        have hMR : ∀ e ∈ M, ∀ a ∈ e, a ∈ R → e ⊆ R := fun e he a ha haR =>
          comp_closed hE2 t (Finset.mem_union_left _ he) ha haR
        have hNR : ∀ e ∈ N0, ∀ a ∈ e, a ∈ R → e ⊆ R := fun e he a ha haR =>
          comp_closed hE2 t (Finset.mem_union_right _ he) ha haR
        have hM' := isM_swap M N0 hMm hN0 R hMR hNR
        have hN' := isM_swap N0 M hN0 hMm R hNR hMR
        have hchiR : ∀ L : Finset (Finset α), (∀ e ∈ L, e ∈ posE w) →
            ∑ e ∈ L.filter (fun e => e ⊆ R), chi e = (L.filter (fun e => e ⊆ R)).card := by
          intro L hL
          rw [Finset.card_eq_sum_ones]
          apply Finset.sum_congr rfl
          intro e he
          rw [Finset.mem_filter] at he
          rw [hchi, if_pos ⟨he.2.trans hRC, hL e he.1⟩]
        have hcount : (N0.filter (fun e => e ⊆ R)).card ≤ (M.filter (fun e => e ⊆ R)).card ∧
            ∃ x, (x = u ∨ x = v) ∧ x ∉ R := by
          have h1 := comp_connected E hE2 t
          have h2 : (E.filter (fun e => e ⊆ R)).card ≤
              (M.filter (fun e => e ⊆ R)).card + (N0.filter (fun e => e ⊆ R)).card := by
            simp only [E, Finset.filter_union]
            exact Finset.card_union_le _ _
          have hcov : ∀ L : Finset (Finset α), IsM L → ∀ B : Finset α,
              B ⊆ R → (∀ b ∈ B, ∀ e ∈ L, b ∉ e) → 2 * (L.filter (fun e => e ⊆ R)).card + B.card ≤ R.card := by
            intro L hL B hB hBL
            rw [← matched_card _ (hL.mono (Finset.filter_subset _ _)), ← Finset.card_union_of_disjoint]
            · apply Finset.card_le_card
              apply Finset.union_subset _ hB
              intro a ha
              rw [Finset.mem_biUnion] at ha
              obtain ⟨e, he, hae⟩ := ha
              exact (Finset.mem_filter.1 he).2 hae
            · rw [Finset.disjoint_left]
              intro a ha haB
              rw [Finset.mem_biUnion] at ha
              obtain ⟨e, he, hae⟩ := ha
              exact hBL a haB e (Finset.mem_filter.1 he).1 hae
          have h3 := hcov N0 hN0 {t} (by simpa [R] using self_comp E t) (by
            intro b hb e he
            rw [Finset.mem_singleton] at hb
            subst hb
            exact hNt e he)
          rw [Finset.card_singleton] at h3
          change R.card ≤ (E.filter (fun e => e ⊆ R)).card + 1 at h1
          refine ⟨by omega, ?_⟩
          by_contra hc
          have huR : u ∈ R := by
            by_contra h
            exact hc ⟨u, Or.inl rfl, h⟩
          have hvR : v ∈ R := by
            by_contra h
            exact hc ⟨v, Or.inr rfl, h⟩
          have h4 := hcov M hMm {u, v} (by
            intro a ha
            simp only [Finset.mem_insert, Finset.mem_singleton] at ha
            rcases ha with rfl | rfl <;> assumption) (by
            intro b hb e he
            simp only [Finset.mem_insert, Finset.mem_singleton] at hb
            rcases hb with rfl | rfl
            · exact hMu e he
            · exact hMv e he)
          rw [Finset.card_pair huv] at h4
          omega
        obtain ⟨hcard, x, hx, hxR⟩ := hcount
        have hsplit : ∀ (L : Finset (Finset α)) (f : Finset α → ℕ), ∑ e ∈ L, f e =
            ∑ e ∈ L.filter (fun e => ¬ e ⊆ R), f e + ∑ e ∈ L.filter (fun e => e ⊆ R), f e := by
          intro L f
          rw [add_comm]
          exact (Finset.sum_filter_add_sum_filter_not L (fun e => e ⊆ R) f).symm
        have a1 := sum_swap M N0 hMm hN0 R hMR w'
        have a2 := sum_swap M N0 hMm hN0 R hMR chi
        have a3 := sum_swap N0 M hN0 hMm R hNR w
        have b1 := hsplit M w'
        have b2 := hsplit M chi
        have b3 := hsplit M w
        have b4 := hsplit N0 w
        have c1 := hsum (M.filter (fun e => e ⊆ R))
        have c2 := hsum (N0.filter (fun e => e ⊆ R))
        have d1 := hchiR M hMpos
        have d2 := hchiR N0 hNpos
        have c3 := hsum (N0.filter (fun e => e ⊆ R))
        have l1 := le_nu w' hM'
        have l2 := le_nu w hN'
        have e1 : ∑ e ∈ M.filter (fun e => ¬ e ⊆ R) ∪ N0.filter (fun e => e ⊆ R), w' e = nu w' := by
          omega
        have e2 : ∑ e ∈ M.filter (fun e => ¬ e ⊆ R) ∪ N0.filter (fun e => e ⊆ R), chi e =
            ∑ e ∈ M0, chi e := by
          have hmem : M.filter (fun e => ¬ e ⊆ R) ∪ N0.filter (fun e => e ⊆ R) ∈ Good := by
            refine Finset.mem_filter.2 ⟨(mem_matchings _).2 hM', ?_, e1⟩
            intro e he
            rcases Finset.mem_union.1 he with h | h
            · exact hMpos e (Finset.mem_filter.1 h).1
            · exact hNpos e (Finset.mem_filter.1 h).1
          have h5 : ∑ e ∈ M.filter (fun e => ¬ e ⊆ R) ∪ N0.filter (fun e => e ⊆ R), chi e ≤
              ∑ e ∈ M0, chi e := hmax _ hmem
          omega
        have hmem : M.filter (fun e => ¬ e ⊆ R) ∪ N0.filter (fun e => e ⊆ R) ∈ Good := by
          refine Finset.mem_filter.2 ⟨(mem_matchings _).2 hM', ?_, e1⟩
          intro e he
          rcases Finset.mem_union.1 he with h | h
          · exact hMpos e (Finset.mem_filter.1 h).1
          · exact hNpos e (Finset.mem_filter.1 h).1
        have htnew : ∀ e ∈ M.filter (fun e => ¬ e ⊆ R) ∪ N0.filter (fun e => e ⊆ R), t ∉ e := by
          intro e he hte
          rcases Finset.mem_union.1 he with h | h
          · rw [Finset.mem_filter] at h
            exact h.2 (hMR e h.1 t hte (self_comp E t))
          · exact hNt e (Finset.mem_filter.1 h).1 hte
        have hxnew : ∀ e ∈ M.filter (fun e => ¬ e ⊆ R) ∪ N0.filter (fun e => e ⊆ R), x ∉ e := by
          intro e he hxe
          rcases Finset.mem_union.1 he with h | h
          · rcases hx with rfl | rfl
            · exact hMu e (Finset.mem_filter.1 h).1 hxe
            · exact hMv e (Finset.mem_filter.1 h).1 hxe
          · exact hxR ((Finset.mem_filter.1 h).2 hxe)
        have htx : t ≠ x := by
          intro h
          exact hxR (h ▸ self_comp E t)
        rcases hx with rfl | rfl
        · exact ih 1 (by omega) ⟨_, hmem, e2, t, x, htC, hu, htx, htnew, hxnew,
            ⟨x, adj_symm hut, rfl⟩⟩
        · exact ih m (by omega) ⟨_, hmem, e2, t, x, htC, hv, htx, htnew, hxnew, htv⟩
  obtain ⟨hM0m, hM0pos, hM0w⟩ := Finset.mem_filter.1 hM0
  rw [mem_matchings] at hM0m
  have hconn : ∀ u ∈ C, ∀ v ∈ C, ∃ d, Reach (posE w) d u v := by
    intro u hu v hv
    rw [hp] at hu hv
    obtain ⟨n, hn⟩ := (mem_comp _ _ _).1 hu
    obtain ⟨m, hm⟩ := (mem_comp _ _ _).1 hv
    exact reach_trans (reach_symm hn) hm
  have hone : (C.filter (fun v => ∀ e ∈ M0, v ∉ e)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro u hu v hv
    rw [Finset.mem_filter] at hu hv
    by_contra huv
    obtain ⟨d, hd⟩ := hconn u hu.1 v hv.1
    exact hnobad d ⟨M0, hM0, rfl, u, v, hu.1, hv.1, huv, hu.2, hv.2, hd⟩
  have hlow : C.card ≤ 2 * (∑ e ∈ M0, chi e) + 1 := by
    rw [hchiM, ← matched_card _ (hM0m.mono (Finset.filter_subset _ _))]
    have : C ⊆ (M0.filter (fun e => e ⊆ C ∧ e ∈ posE w)).biUnion id ∪
        C.filter (fun v => ∀ e ∈ M0, v ∉ e) := by
      intro v hv
      rw [Finset.mem_union]
      by_cases h : ∀ e ∈ M0, v ∉ e
      · exact Or.inr (Finset.mem_filter.2 ⟨hv, h⟩)
      · left
        simp only [not_forall, not_not] at h
        obtain ⟨e, he, hve⟩ := h
        rw [Finset.mem_biUnion]
        exact ⟨e, Finset.mem_filter.2 ⟨he, hclosed e (hM0pos e he) v hve hv, hM0pos e he⟩, hve⟩
    have := (Finset.card_le_card this).trans (Finset.card_union_le _ _)
    omega
  have hge : nu w' + C.card / 2 ≤ nu w := by
    have h1 := le_nu w hM0m
    have h2 := hsum M0
    omega
  refine ⟨hge, ?_⟩
  by_contra hodd
  obtain ⟨N0, hN0, hN0w, hN0p⟩ := hmiss p
  have hpC : p ∈ C := hp ▸ self_comp _ _
  have h1 : 2 * (∑ e ∈ N0, chi e) + 1 ≤ C.card := by
    rw [hchiM, ← matched_card _ (hN0.mono (Finset.filter_subset _ _))]
    have : (N0.filter (fun e => e ⊆ C ∧ e ∈ posE w)).biUnion id ⊆ C.erase p := by
      intro v hv
      rw [Finset.mem_biUnion] at hv
      obtain ⟨e, he, hve⟩ := hv
      rw [Finset.mem_filter] at he
      rw [Finset.mem_erase]
      refine ⟨?_, he.2.1 hve⟩
      intro h
      subst h
      exact (hN0p e he.1).2 hve
    have := Finset.card_le_card this
    rw [Finset.card_erase_of_mem hpC] at this
    have : 0 < C.card := Finset.card_pos.2 ⟨p, hpC⟩
    omega
  have h2 := le_nu w' hN0
  have h3 := hsum N0
  omega

theorem cm (w : Finset α → ℕ) : ∃ y z, Dual w y z ∧ cost y z ≤ nu w := by
  classical
  induction hs : ∑ e, w e using Nat.strong_induction_on generalizing w with
  | _ s ih =>
    by_cases h0 : posE w = ∅
    · refine ⟨fun _ => 0, fun _ => 0, ⟨by simp, ?_⟩, by simp [cost]⟩
      intro e he
      have : e ∉ posE w := by simp [h0]
      rw [mem_posE] at this
      have : w e = 0 := by omega
      omega
    have hlt : ∀ w' : Finset α → ℕ, (∀ e, w' e ≤ w e) → (∃ e, w' e < w e) →
        ∃ y z, Dual w' y z ∧ cost y z ≤ nu w' := by
      intro w' h1 ⟨e, he⟩
      refine ih (∑ e, w' e) ?_ w' rfl
      rw [← hs]
      exact Finset.sum_lt_sum (fun e _ => h1 e) ⟨e, Finset.mem_univ _, he⟩
    obtain ⟨e0, he0⟩ := Finset.nonempty_iff_ne_empty.2 h0
    have he0' := (mem_posE w e0).1 he0
    by_cases hv : ∃ v : α, ∀ N, IsM N → ∑ e ∈ N, w e = nu w → ∃ e ∈ N, v ∈ e ∧ 0 < w e
    · obtain ⟨v, hv⟩ := hv
      let w' : Finset α → ℕ := fun e => if v ∈ e then w e - 1 else w e
      have hle : ∀ e, w' e ≤ w e := fun e => by
        simp only [w']
        split <;> omega
      have hex : ∃ e, w' e < w e := by
        obtain ⟨N, hN, hNw⟩ := exists_nu w
        obtain ⟨e, _, hve, hpos⟩ := hv N hN hNw
        refine ⟨e, ?_⟩
        simp only [w', if_pos hve]
        omega
      have hnu : nu w' + 1 ≤ nu w := by
        obtain ⟨M, hM, hMw⟩ := exists_nu w'
        have h1 := le_nu w hM
        have h2 : ∑ e ∈ M, w' e ≤ ∑ e ∈ M, w e := Finset.sum_le_sum fun e _ => hle e
        by_cases h3 : ∑ e ∈ M, w e = nu w
        · obtain ⟨e, he, hve, hpos⟩ := hv M hM h3
          have : ∑ e ∈ M, w' e < ∑ e ∈ M, w e := by
            refine Finset.sum_lt_sum (fun e _ => hle e) ⟨e, he, ?_⟩
            simp only [w', if_pos hve]
            omega
          omega
        · omega
      obtain ⟨y, z, hD, hc⟩ := hlt w' hle hex
      refine ⟨fun u => y u + if u = v then 1 else 0, z, ⟨hD.1, ?_⟩, ?_⟩
      · intro e he
        have h := hD.2 e he
        have h1 : w e ≤ w' e + if v ∈ e then 1 else 0 := by
          simp only [w']
          split <;> omega
        rw [Finset.sum_add_distrib, Finset.sum_ite_eq' e v (fun _ => 1)]
        omega
      · unfold cost at hc ⊢
        rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ v (fun _ => 1)]
        simp only [Finset.mem_univ, if_true]
        omega
    · have hmiss : ∀ v : α, ∃ N, IsM N ∧ (∑ e ∈ N, w e = nu w) ∧ ∀ e ∈ N, e ∈ posE w ∧ v ∉ e := by
        intro v
        have : ¬ ∀ N, IsM N → ∑ e ∈ N, w e = nu w → ∃ e ∈ N, v ∈ e ∧ 0 < w e :=
          fun h => hv ⟨v, h⟩
        simp only [not_forall] at this
        obtain ⟨N, hN, hNw, hno⟩ := this
        refine ⟨N.filter (fun e => 0 < w e), hN.mono (Finset.filter_subset _ _), ?_, ?_⟩
        · rw [← hNw]
          apply Finset.sum_filter_of_ne
          intro e _ h
          omega
        · intro e he
          rw [Finset.mem_filter] at he
          exact ⟨(mem_posE _ _).2 ⟨hN.1 e he.1, he.2⟩, fun h => hno ⟨e, he.1, h, he.2⟩⟩
      have : e0.Nonempty := Finset.card_pos.1 (by omega)
      obtain ⟨p, hpe⟩ := this
      let C := comp (posE w) p
      let chi : Finset α → ℕ := fun e => if e ⊆ C ∧ e ∈ posE w then 1 else 0
      let w' : Finset α → ℕ := fun e => w e - chi e
      have hchiw : ∀ e, chi e ≤ w e := by
        intro e
        simp only [chi]
        split
        · rename_i h
          have := (mem_posE _ _).1 h.2
          omega
        · omega
      have hww : ∀ e, w e = w' e + chi e := by
        intro e
        have := hchiw e
        simp only [w']
        omega
      have he0C : e0 ⊆ C :=
        comp_closed (fun e he => ((mem_posE w e).1 he).1) p he0 hpe (self_comp _ _)
      have hex : ∃ e, w' e < w e := by
        refine ⟨e0, ?_⟩
        have : chi e0 = 1 := by simp only [chi, if_pos (And.intro he0C he0)]
        have := hww e0
        omega
      obtain ⟨hnu, hodd⟩ := cm_core w w' C chi ⟨p, rfl⟩ (fun _ => rfl) hww hmiss
      obtain ⟨y, z, hD, hc⟩ := hlt w' (fun e => by have := hww e; omega) hex
      refine ⟨y, fun U => z U + if U = C then 1 else 0, ⟨?_, ?_⟩, ?_⟩
      · intro U hU
        by_cases h : U = C
        · rw [h]
          exact hodd
        · exact hD.1 U (by simpa [h] using hU)
      · intro e he
        have h := hD.2 e he
        have h1 : chi e ≤ if e ⊆ C then 1 else 0 := by
          simp only [chi]
          by_cases h2 : e ⊆ C
          · rw [if_pos h2]
            split <;> omega
          · simp [h2]
        have h2 := hww e
        rw [Finset.sum_add_distrib, Finset.sum_ite_eq' (Finset.univ.filter (fun T => e ⊆ T)) C (fun _ => 1)]
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        omega
      · unfold cost at hc ⊢
        simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero]
        rw [Finset.sum_ite_eq' Finset.univ C (fun U => U.card / 2)]
        simp only [Finset.mem_univ, if_true]
        omega

theorem reduce (z : Finset α → ℚ) (h : Finset α → ℚ) (hz : ∀ U, 0 ≤ z U) :
    ∃ z' : Finset α → ℚ, (∀ U, 0 ≤ z' U) ∧ (∀ U, z' U ≠ 0 → z U ≠ 0) ∧
      (Finset.univ.filter (fun U => z' U ≠ 0)).card ≤ (Finset.univ.powersetCard 2 : Finset (Finset α)).card ∧
      (∀ e : Finset α, e.card = 2 → ∑ U ∈ Finset.univ.filter (fun T => e ⊆ T), z U ≤
        ∑ U ∈ Finset.univ.filter (fun T => e ⊆ T), z' U) ∧
      ∑ U, h U * z' U ≤ ∑ U, h U * z U ∨ (∃ U, h U < 0) := by
  classical
  by_cases hh : ∃ U, h U < 0
  · exact ⟨z, Or.inr hh⟩
  have hh' : ∀ U, 0 ≤ h U := fun U => le_of_not_gt fun c => hh ⟨U, c⟩
  suffices H : ∀ n, ∀ z : Finset α → ℚ, (∀ U, 0 ≤ z U) →
      (Finset.univ.filter (fun U => z U ≠ 0)).card = n →
      ∃ z' : Finset α → ℚ, (∀ U, 0 ≤ z' U) ∧ (∀ U, z' U ≠ 0 → z U ≠ 0) ∧
        (Finset.univ.filter (fun U => z' U ≠ 0)).card ≤ (Finset.univ.powersetCard 2 : Finset (Finset α)).card ∧
        (∀ e : Finset α, e.card = 2 → ∑ U ∈ Finset.univ.filter (fun T => e ⊆ T), z U ≤
          ∑ U ∈ Finset.univ.filter (fun T => e ⊆ T), z' U) ∧
        ∑ U, h U * z' U ≤ ∑ U, h U * z U by
    obtain ⟨z', h1, h2, h3, h4, h5⟩ := H _ z hz rfl
    exact ⟨z', Or.inl ⟨h1, h2, h3, h4, h5⟩⟩
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro z hz hn
    by_cases hsmall : n ≤ (Finset.univ.powersetCard 2 : Finset (Finset α)).card
    · exact ⟨z, hz, fun _ h => h, hn ▸ hsmall, fun _ _ => le_rfl, le_rfl⟩
    have step : ∀ z1 : Finset α → ℚ, (∀ U, 0 ≤ z1 U) → (∀ U, z1 U ≠ 0 → z U ≠ 0) →
        (∃ U, z U ≠ 0 ∧ z1 U = 0) →
        (∀ e : Finset α, e.card = 2 → ∑ U ∈ Finset.univ.filter (fun T => e ⊆ T), z U ≤
          ∑ U ∈ Finset.univ.filter (fun T => e ⊆ T), z1 U) →
        (∑ U, h U * z1 U ≤ ∑ U, h U * z U) →
        ∃ z' : Finset α → ℚ, (∀ U, 0 ≤ z' U) ∧ (∀ U, z' U ≠ 0 → z U ≠ 0) ∧
          (Finset.univ.filter (fun U => z' U ≠ 0)).card ≤ (Finset.univ.powersetCard 2 : Finset (Finset α)).card ∧
          (∀ e : Finset α, e.card = 2 → ∑ U ∈ Finset.univ.filter (fun T => e ⊆ T), z U ≤
            ∑ U ∈ Finset.univ.filter (fun T => e ⊆ T), z' U) ∧
          ∑ U, h U * z' U ≤ ∑ U, h U * z U := by
      intro z1 h1 h2 ⟨U0, hU0, hU0'⟩ h3 h4
      have hlt : (Finset.univ.filter (fun U => z1 U ≠ 0)).card < n := by
        rw [← hn]
        apply Finset.card_lt_card
        refine (Finset.ssubset_iff_of_subset ?_).2 ⟨U0, by simpa using hU0, by simpa using hU0'⟩
        intro U hU
        rw [Finset.mem_filter] at hU ⊢
        exact ⟨hU.1, h2 U hU.2⟩
      obtain ⟨z', a1, a2, a3, a4, a5⟩ := ih _ hlt z1 h1 rfl
      exact ⟨z', a1, fun U hU => h2 U (a2 U hU), a3, fun e he => (h3 e he).trans (a4 e he), a5.trans h4⟩
    by_cases htriv : ∃ U, z U ≠ 0 ∧ ∀ e : Finset α, e.card = 2 → ¬ e ⊆ U
    · obtain ⟨U0, hU0, hno⟩ := htriv
      refine step (fun U => if U = U0 then 0 else z U) ?_ ?_ ⟨U0, hU0, by simp⟩ ?_ ?_
      · intro U
        split
        · exact le_rfl
        · exact hz U
      · intro U hU
        split at hU
        · exact absurd rfl hU
        · exact hU
      · intro e he
        apply le_of_eq
        apply Finset.sum_congr rfl
        intro U hU
        rw [Finset.mem_filter] at hU
        rw [if_neg]
        intro c
        exact hno e he (c ▸ hU.2)
      · apply Finset.sum_le_sum
        intro U _
        apply mul_le_mul_of_nonneg_left _ (hh' U)
        split
        · exact hz U
        · exact le_rfl
    let S := Finset.univ.filter (fun U : Finset α => z U ≠ 0)
    let P := (Finset.univ.powersetCard 2 : Finset (Finset α))
    let vec : S → (P → ℚ) := fun U e => if e.1 ⊆ U.1 then 1 else 0
    have hdep : ¬ LinearIndependent ℚ vec := by
      intro hli
      have := hli.fintype_card_le_finrank
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe, Fintype.card_coe] at this
      have hS : S.card = n := hn
      exact hsmall (hS ▸ this)
    obtain ⟨g, hg, i, hi⟩ := Fintype.not_linearIndependent_iff.1 hdep
    have hg' : ∃ g : S → ℚ, (∑ U, g U • vec U = 0) ∧ (∃ i, g i ≠ 0) ∧ 0 ≤ ∑ U : S, h U.1 * g U := by
      by_cases hs : 0 ≤ ∑ U : S, h U.1 * g U
      · exact ⟨g, hg, ⟨i, hi⟩, hs⟩
      · refine ⟨fun U => - g U, ?_, ⟨i, by simpa using hi⟩, ?_⟩
        · simp only [neg_smul, Finset.sum_neg_distrib, hg, neg_zero]
        · simp only [mul_neg, Finset.sum_neg_distrib]
          linarith
    obtain ⟨g, hg, ⟨i, hi⟩, hgs⟩ := hg'
    let G : Finset α → ℚ := fun U => if hU : U ∈ S then g ⟨U, hU⟩ else 0
    have hGS : ∀ U : S, G U.1 = g U := fun U => by simp only [G, dif_pos U.2, Subtype.coe_eta]
    have hG0 : ∀ U, U ∉ S → G U = 0 := fun U hU => by simp only [G, dif_neg hU]
    have hGsum : ∀ f : Finset α → ℚ, ∑ U, f U * G U = ∑ U : S, f U.1 * g U := by
      intro f
      have h1 : ∑ U ∈ S, f U * G U = ∑ U, f U * G U := by
        apply Finset.sum_subset (Finset.subset_univ _)
        intro U _ hU
        rw [hG0 U hU, mul_zero]
      rw [← h1, ← Finset.sum_coe_sort S (fun U => f U * G U)]
      exact Finset.sum_congr rfl fun U _ => by rw [hGS]
    have hcover : ∀ e : Finset α, e.card = 2 → ∑ U ∈ Finset.univ.filter (fun T => e ⊆ T), G U = 0 := by
      intro e he
      have heP : e ∈ P := Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, he⟩
      have := congrFun hg ⟨e, heP⟩
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, vec, Pi.zero_apply] at this
      rw [Finset.sum_filter]
      have h2 := hGsum (fun U => if e ⊆ U then 1 else 0)
      simp only [ite_mul, one_mul, zero_mul] at h2
      rw [h2]
      refine Eq.trans ?_ this
      exact Finset.sum_congr rfl fun U _ => by rw [mul_ite, mul_one, mul_zero]
    have hpos : ∃ U, 0 < G U := by
      by_contra hc
      have hc' : ∀ U, G U ≤ 0 := fun U => le_of_not_gt fun c => hc ⟨U, c⟩
      have hiS : i.1 ∈ S := i.2
      have hex : ∃ e : Finset α, e.card = 2 ∧ e ⊆ i.1 := by
        by_contra c
        exact htriv ⟨i.1, (Finset.mem_filter.1 hiS).2, fun e he hs => c ⟨e, he, hs⟩⟩
      obtain ⟨e, he, hei⟩ := hex
      have h0 := hcover e he
      have := (Finset.sum_eq_zero_iff_of_nonpos (fun U _ => hc' U)).1 h0 i.1
        (Finset.mem_filter.2 ⟨Finset.mem_univ _, hei⟩)
      rw [hGS] at this
      exact hi this
    let Q := Finset.univ.filter (fun U => 0 < G U)
    have hQ : Q.Nonempty := by
      obtain ⟨U, hU⟩ := hpos
      exact ⟨U, Finset.mem_filter.2 ⟨Finset.mem_univ _, hU⟩⟩
    obtain ⟨U0, hU0, hmin⟩ := Finset.exists_min_image Q (fun U => z U / G U) hQ
    have hU0p : 0 < G U0 := (Finset.mem_filter.1 hU0).2
    let t := z U0 / G U0
    have ht : 0 ≤ t := div_nonneg (hz U0) hU0p.le
    have hU0z : z U0 ≠ 0 := by
      intro c
      have : U0 ∉ S := by simp [S, c]
      rw [hG0 U0 this] at hU0p
      exact lt_irrefl _ hU0p
    refine step (fun U => z U - t * G U) ?_ ?_ ⟨U0, hU0z, ?_⟩ ?_ ?_
    · intro U
      by_cases hp : 0 < G U
      · have := hmin U (Finset.mem_filter.2 ⟨Finset.mem_univ _, hp⟩)
        have : t * G U ≤ z U := (le_div_iff₀ hp).1 this
        linarith
      · have : t * G U ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht (le_of_not_gt hp)
        have := hz U
        linarith
    · intro U hU c
      have : U ∉ S := by simp [S, c]
      apply hU
      rw [c, hG0 U this, mul_zero, sub_zero]
    · simp only [t]
      rw [div_mul_cancel₀ _ hU0p.ne', sub_self]
    · intro e he
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hcover e he, mul_zero, sub_zero]
    · have h1 : ∑ U, h U * (z U - t * G U) = ∑ U, h U * z U - t * ∑ U, h U * G U := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun U _ => by ring
      rw [h1, hGsum]
      have := mul_nonneg ht hgs
      linarith

end duality

section comb

variable {k q : ℕ} (fixed target : Fin q → Bool) (D : Fin q → Finset (Finset (Fin k)))

def errF (M : Finset (Finset (Fin k))) : ℕ :=
  (Finset.univ.filter (fun t : Fin q => (fixed t || decide ((M ∩ D t).Nonempty)) ≠ target t)).card

def signedF (S : Finset (Finset (Fin k))) : Int :=
  ((Finset.univ.filter (fun t : Fin q => fixed t = false ∧ S ⊆ D t ∧ target t = true)).card : Int) -
  ((Finset.univ.filter (fun t : Fin q => fixed t = false ∧ S ⊆ D t ∧ target t = false)).card : Int)

theorem signedF_eq (S : Finset (Finset (Fin k))) :
    signedF fixed target D S = ∑ t : Fin q,
      (if fixed t = false ∧ S ⊆ D t then (if target t = true then (1 : Int) else -1) else 0) := by
  unfold signedF
  rw [Finset.card_filter, Finset.card_filter, Nat.cast_sum, Nat.cast_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro t _
  by_cases h1 : fixed t = false <;> by_cases h2 : S ⊆ D t <;> cases h3 : target t <;> simp [h1, h2]

theorem errF_eq (M : Finset (Finset (Fin k))) :
    (errF fixed target D M : Int) = ∑ t : Fin q,
      (if (fixed t || decide ((M ∩ D t).Nonempty)) ≠ target t then (1 : Int) else 0) := by
  unfold errF
  rw [Finset.card_filter, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro t _
  split <;> simp

theorem second_diff (M : Finset (Finset (Fin k))) (e e' : Finset (Fin k))
    (h : ∀ T ⊆ M, signedF fixed target D (insert e (insert e' T)) = 0) :
    (errF fixed target D (insert e (insert e' M)) : Int) + errF fixed target D M =
      errF fixed target D (insert e M) + errF fixed target D (insert e' M) := by
  have key : ∑ t : Fin q, (if fixed t = false ∧ e ∈ D t ∧ e' ∈ D t ∧ M ∩ D t = ∅ then
      (if target t = true then (1 : Int) else -1) else 0) = 0 := by
    have h0 : ∑ T ∈ M.powerset, (-1 : Int) ^ T.card * signedF fixed target D (insert e (insert e' T)) = 0 := by
      apply Finset.sum_eq_zero
      intro T hT
      rw [h T (Finset.mem_powerset.1 hT), mul_zero]
    simp only [signedF_eq, Finset.mul_sum] at h0
    rw [Finset.sum_comm] at h0
    refine Eq.trans ?_ h0
    apply Finset.sum_congr rfl
    intro t _
    have hpow : M.powerset.filter (fun T => T ⊆ D t) = (M ∩ D t).powerset := by
      ext T
      simp [Finset.subset_inter_iff]
    have h1 : ∀ T ∈ M.powerset,
        (-1 : Int) ^ T.card * (if fixed t = false ∧ insert e (insert e' T) ⊆ D t then
          (if target t = true then (1 : Int) else -1) else 0) =
        (if T ⊆ D t then (-1 : Int) ^ T.card else 0) *
          (if fixed t = false ∧ e ∈ D t ∧ e' ∈ D t then (if target t = true then (1 : Int) else -1) else 0) := by
      intro T _
      by_cases a : T ⊆ D t <;> by_cases b : fixed t = false <;> by_cases c : e ∈ D t <;>
        by_cases d : e' ∈ D t <;> simp [Finset.insert_subset_iff, a, b, c, d]
    rw [Finset.sum_congr rfl h1, ← Finset.sum_mul, ← Finset.sum_filter, hpow,
      Finset.sum_powerset_neg_one_pow_card]
    by_cases a : M ∩ D t = ∅ <;> by_cases b : fixed t = false <;> by_cases c : e ∈ D t <;>
        by_cases d : e' ∈ D t <;> simp [a, b, c, d]
  have hpt : ∀ t : Fin q,
      ((if (fixed t || decide ((insert e (insert e' M) ∩ D t).Nonempty)) ≠ target t then (1 : Int) else 0) +
        (if (fixed t || decide ((M ∩ D t).Nonempty)) ≠ target t then (1 : Int) else 0)) =
      ((if (fixed t || decide ((insert e M ∩ D t).Nonempty)) ≠ target t then (1 : Int) else 0) +
        (if (fixed t || decide ((insert e' M ∩ D t).Nonempty)) ≠ target t then (1 : Int) else 0)) +
      (if fixed t = false ∧ e ∈ D t ∧ e' ∈ D t ∧ M ∩ D t = ∅ then
        (if target t = true then (1 : Int) else -1) else 0) := by
    intro t
    have hne : ∀ (a : Finset (Fin k)) (L : Finset (Finset (Fin k))),
        (insert a L ∩ D t).Nonempty ↔ a ∈ D t ∨ (L ∩ D t).Nonempty := by
      intro a L
      by_cases ha : a ∈ D t
      · simp [Finset.insert_inter_of_mem ha, ha]
      · simp [Finset.insert_inter_of_notMem ha, ha]
    simp only [hne, ← Finset.not_nonempty_iff_eq_empty]
    by_cases a : (M ∩ D t).Nonempty <;> cases b : fixed t <;> by_cases c : e ∈ D t <;>
        by_cases d : e' ∈ D t <;> cases f : target t <;> simp [a, c, d]
  simp only [errF_eq]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.sum_congr rfl (fun t _ => hpt t),
    Finset.sum_add_distrib, key, add_zero]

theorem additive (I : Finset (Finset (Fin k)))
    (hsig : ∀ S, IsM S → signedF fixed target D S ≠ 0 → (S \ I).card ≤ 1)
    (K N : Finset (Finset (Fin k))) (hKI : K ⊆ I) (hNI : ∀ e ∈ N, e ∉ I) (hM : IsM (K ∪ N)) :
    (errF fixed target D (K ∪ N) : Int) = errF fixed target D K -
      ∑ e ∈ N, ((errF fixed target D K : Int) - errF fixed target D (insert e K)) := by
  have delta : ∀ (e : Finset (Fin k)) (L : Finset (Finset (Fin k))), e ∉ I → e ∉ L → (∀ g ∈ L, g ∉ I) →
      IsM (insert e (K ∪ L)) →
      (errF fixed target D (insert e (K ∪ L)) : Int) - errF fixed target D (K ∪ L) =
        errF fixed target D (insert e K) - errF fixed target D K := by
    intro e L heI
    induction L using Finset.induction_on with
    | empty => intro _ _ _; rw [Finset.union_empty]
    | @insert a L haL ih =>
      intro heL hLI hm
      rw [Finset.mem_insert, not_or] at heL
      have haI : a ∉ I := hLI a (Finset.mem_insert_self _ _)
      rw [Finset.union_insert] at hm ⊢
      have h2 := second_diff fixed target D (K ∪ L) e a (by
        intro T hT
        by_contra hne
        have hsub : insert e (insert a T) ⊆ insert e (insert a (K ∪ L)) :=
          Finset.insert_subset_insert _ (Finset.insert_subset_insert _ hT)
        have := hsig _ (hm.mono hsub) hne
        have h2 : ({e, a} : Finset (Finset (Fin k))) ⊆ insert e (insert a T) \ I := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl <;> simp [heI, haI]
        have h3 := Finset.card_le_card h2
        rw [Finset.card_pair heL.1] at h3
        omega)
      have h3 := ih heL.2 (fun g hg => hLI g (Finset.mem_insert_of_mem hg))
        (hm.mono (Finset.insert_subset_insert _ (Finset.subset_insert _ _)))
      omega
  have : ∀ L : Finset (Finset (Fin k)), L ⊆ N → (errF fixed target D (K ∪ L) : Int) = errF fixed target D K -
      ∑ e ∈ L, ((errF fixed target D K : Int) - errF fixed target D (insert e K)) := by
    intro L
    induction L using Finset.induction_on with
    | empty => intro _; simp
    | @insert a L haL ih =>
      intro hsub
      rw [Finset.insert_subset_iff] at hsub
      have h1 := ih hsub.2
      have h2 := delta a L (hNI a hsub.1) haL (fun g hg => hNI g (hsub.2 hg)) (by
        apply hM.mono
        apply Finset.insert_subset (Finset.mem_union_right _ hsub.1)
        exact Finset.union_subset_union_right hsub.2)
      rw [Finset.union_insert, Finset.sum_insert haL]
      omega
  exact this N (Finset.Subset.refl _)

theorem comb (I : Finset (Finset (Fin k))) (b : ℕ)
    (hsig : ∀ S, IsM S → signedF fixed target D S ≠ 0 → (S \ I).card ≤ 1) :
    (∀ M, IsM M → b ≤ errF fixed target D M) ↔
      ∀ K ⊆ I, IsM K → ∃ (y : Fin k → ℚ) (z : Finset (Fin k) → ℚ),
        (∀ v, 0 ≤ y v) ∧ (∀ U, 0 ≤ z U) ∧
        ((Finset.univ.filter (fun U : Finset (Fin k) => U.card % 2 = 1)).filter (fun U => z U ≠ 0)).card ≤ k*(k-1)/2 ∧
        (∀ e : Finset (Fin k), e.card = 2 → e ∉ I → (∀ g ∈ K, Disjoint e g) →
          (errF fixed target D K : ℚ) - (errF fixed target D (insert e K) : ℚ) ≤
            (∑ v ∈ e, y v) + ∑ U ∈ (Finset.univ.filter (fun U : Finset (Fin k) => U.card % 2 = 1)).filter (fun T => e ⊆ T), z U) ∧
        (∑ v : Fin k, y v) + (∑ U ∈ Finset.univ.filter (fun U : Finset (Fin k) => U.card % 2 = 1), ((U.card/2 : ℕ) : ℚ)*z U) ≤
          (errF fixed target D K : ℚ) - (b : ℚ) := by
  classical
  have hodd : ∀ (f : Finset (Fin k) → ℚ), (∀ U, f U ≠ 0 → U.card % 2 = 1) → ∀ p : Finset (Fin k) → Prop,
      ∀ [DecidablePred p], ∑ U ∈ (Finset.univ.filter (fun U : Finset (Fin k) => U.card % 2 = 1)).filter p, f U =
        ∑ U ∈ Finset.univ.filter p, f U := by
    intro f hf p _
    apply Finset.sum_subset
    · intro U hU
      rw [Finset.mem_filter] at hU ⊢
      exact ⟨Finset.mem_univ _, hU.2⟩
    · intro U hU hn
      by_contra h
      apply hn
      rw [Finset.mem_filter] at hU ⊢
      exact ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, hf U h⟩, hU.2⟩
  have hun : ∀ K : Finset (Finset (Fin k)), IsM K → ∀ N : Finset (Finset (Fin k)), IsM N →
      (∀ e ∈ N, ∀ g ∈ K, Disjoint e g) → IsM (K ∪ N) := by
    intro K hK N hN hd
    refine ⟨?_, ?_⟩
    · intro e he
      rcases Finset.mem_union.1 he with h | h
      · exact hK.1 e h
      · exact hN.1 e h
    · intro e he g hg hne
      rcases Finset.mem_union.1 he with h | h <;> rcases Finset.mem_union.1 hg with h' | h'
      · exact hK.2 e h g h' hne
      · exact (hd g h' e h).symm
      · exact hd e h g h'
      · exact hN.2 e h g h' hne
  constructor
  · intro hb K hKI hK
    let w : Finset (Fin k) → ℕ := fun e =>
      if e.card = 2 ∧ e ∉ I ∧ ∀ g ∈ K, Disjoint e g then
        ((errF fixed target D K : Int) - errF fixed target D (insert e K)).toNat else 0
    have hbK := hb K hK
    have hnu : nu w ≤ errF fixed target D K - b := by
      apply nu_le
      intro M hM
      let N := M.filter (fun e => 0 < w e)
      have hsum : ∑ e ∈ M, w e = ∑ e ∈ N, w e := by
        symm
        apply Finset.sum_filter_of_ne
        intro e _ h
        omega
      have hN : ∀ e ∈ N, e.card = 2 ∧ e ∉ I ∧ ∀ g ∈ K, Disjoint e g := by
        intro e he
        rw [Finset.mem_filter] at he
        by_contra h
        simp only [w, if_neg h] at he
        exact lt_irrefl 0 he.2
      have hNm : IsM N := hM.mono (Finset.filter_subset _ _)
      have hKN := hun K hK N hNm (fun e he => (hN e he).2.2)
      have hadd := additive fixed target D I hsig K N hKI (fun e he => (hN e he).2.1) hKN
      have hcast : ((∑ e ∈ N, w e : ℕ) : Int) =
          ∑ e ∈ N, ((errF fixed target D K : Int) - errF fixed target D (insert e K)) := by
        rw [Nat.cast_sum]
        apply Finset.sum_congr rfl
        intro e he
        have h1 := (Finset.mem_filter.1 he).2
        simp only [w, if_pos (hN e he)] at h1 ⊢
        omega
      have := hb _ hKN
      omega
    obtain ⟨y, z, hD, hc⟩ := cm w
    let yq : Fin k → ℚ := fun v => (y v : ℚ)
    let zq : Finset (Fin k) → ℚ := fun U => (z U : ℚ)
    rcases reduce zq (fun U => ((U.card / 2 : ℕ) : ℚ)) (fun U => Nat.cast_nonneg _) with
      ⟨z', h⟩
    rcases h with ⟨h1, h2, h3, h4, h5⟩ | ⟨U, hU⟩
    swap
    · exact absurd hU (not_lt.2 (Nat.cast_nonneg _))
    have hz'odd : ∀ U, z' U ≠ 0 → U.card % 2 = 1 := by
      intro U hU
      have := h2 U hU
      exact hD.1 U (by simpa [zq] using this)
    refine ⟨yq, z', fun v => Nat.cast_nonneg _, h1, ?_, ?_, ?_⟩
    · have : ((Finset.univ.filter (fun U : Finset (Fin k) => U.card % 2 = 1)).filter (fun U => z' U ≠ 0)).card ≤
          (Finset.univ.filter (fun U => z' U ≠ 0)).card := by
        apply Finset.card_le_card
        intro U hU
        rw [Finset.mem_filter] at hU ⊢
        exact ⟨Finset.mem_univ _, hU.2⟩
      refine this.trans (h3.trans ?_)
      rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin, Nat.choose_two_right]
    · intro e he heI heK
      have h6 := hD.2 e he
      have h7 : (errF fixed target D K : Int) - errF fixed target D (insert e K) ≤ (w e : Int) := by
        simp only [w, if_pos (And.intro he (And.intro heI heK))]
        exact Int.self_le_toNat _
      have h8 : (errF fixed target D K : ℚ) - (errF fixed target D (insert e K) : ℚ) ≤ (w e : ℚ) := by
        exact_mod_cast h7
      have h9 : (w e : ℚ) ≤ ∑ v ∈ e, yq v + ∑ U ∈ Finset.univ.filter (fun T => e ⊆ T), zq U := by
        simp only [yq, zq]
        exact_mod_cast h6
      rw [hodd z' hz'odd (fun T => e ⊆ T)]
      have h10 := h4 e he
      linarith
    · have h6 : cost y z ≤ errF fixed target D K - b := hc.trans hnu
      have h7 : (cost y z : ℚ) ≤ (errF fixed target D K : ℚ) - b := by
        have : (cost y z : Int) ≤ (errF fixed target D K : Int) - b := by omega
        exact_mod_cast this
      have h8 : (cost y z : ℚ) = ∑ v, yq v + ∑ U : Finset (Fin k), ((U.card / 2 : ℕ) : ℚ) * zq U := by
        unfold cost
        simp only [yq, zq, Nat.cast_add, Nat.cast_sum, Nat.cast_mul]
      have h9 : ∑ U ∈ Finset.univ.filter (fun U : Finset (Fin k) => U.card % 2 = 1), ((U.card/2 : ℕ) : ℚ)*z' U ≤
          ∑ U : Finset (Fin k), ((U.card/2 : ℕ) : ℚ)*z' U :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun U _ _ => mul_nonneg (Nat.cast_nonneg _) (h1 U))
      linarith
  · intro H M hM
    let K := M.filter (fun e => e ∈ I)
    let N := M.filter (fun e => e ∉ I)
    have hMKN : K ∪ N = M := Finset.filter_union_filter_not_eq (fun e => e ∈ I) M
    have hKI : K ⊆ I := fun e he => (Finset.mem_filter.1 he).2
    obtain ⟨y, z, hy, hz, _, hcov, hc⟩ := H K hKI (hM.mono (Finset.filter_subset _ _))
    have hadd := additive fixed target D I hsig K N hKI (fun e he => (Finset.mem_filter.1 he).2)
      (hMKN ▸ hM)
    rw [hMKN] at hadd
    have hNm : IsM N := hM.mono (Finset.filter_subset _ _)
    let O := Finset.univ.filter (fun U : Finset (Fin k) => U.card % 2 = 1)
    have hdisj : (N : Set (Finset (Fin k))).PairwiseDisjoint id := by
      intro a ha c hc hac
      exact hNm.2 a ha c hc hac
    have h1 : ∑ e ∈ N, ((errF fixed target D K : ℚ) - errF fixed target D (insert e K)) ≤
        ∑ e ∈ N, ((∑ v ∈ e, y v) + ∑ U ∈ O.filter (fun T => e ⊆ T), z U) := by
      apply Finset.sum_le_sum
      intro e he
      have he' := Finset.mem_filter.1 he
      apply hcov e (hM.1 e he'.1) he'.2
      intro g hg
      have hg' := Finset.mem_filter.1 hg
      exact hM.2 e he'.1 g hg'.1 (fun c => he'.2 (c ▸ hg'.2))
    have h2 : ∑ e ∈ N, ∑ v ∈ e, y v ≤ ∑ v, y v := by
      have := Finset.sum_biUnion (f := y) hdisj
      simp only [id] at this
      rw [← this]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun v _ _ => hy v)
    have h3 : ∑ e ∈ N, ∑ U ∈ O.filter (fun T => e ⊆ T), z U ≤ ∑ U ∈ O, ((U.card/2 : ℕ) : ℚ) * z U := by
      simp only [Finset.sum_filter]
      rw [Finset.sum_comm]
      apply Finset.sum_le_sum
      intro U _
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_right _ (hz U)
      have h4 : 2 * (N.filter (fun e => e ⊆ U)).card ≤ U.card := by
        rw [← matched_card _ (hNm.mono (Finset.filter_subset _ _))]
        apply Finset.card_le_card
        intro v hv
        rw [Finset.mem_biUnion] at hv
        obtain ⟨e, he, hve⟩ := hv
        exact (Finset.mem_filter.1 he).2 hve
      have h5 : (N.filter (fun e => e ⊆ U)).card ≤ U.card / 2 := by omega
      exact_mod_cast h5
    rw [Finset.sum_add_distrib] at h1
    have h6 : (errF fixed target D M : ℚ) = errF fixed target D K -
        ∑ e ∈ N, ((errF fixed target D K : ℚ) - errF fixed target D (insert e K)) := by
      have := congrArg (fun x : Int => (x : ℚ)) hadd
      simpa only [Int.cast_sub, Int.cast_sum, Int.cast_natCast] using this
    have h7 : (b : ℚ) ≤ errF fixed target D M := by
      change ∑ v, y v + ∑ U ∈ O, ((U.card/2 : ℕ) : ℚ) * z U ≤ _ at hc
      linarith
    exact_mod_cast h7

end comb

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def run (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w

theorem wires_run (C : Circuit) (x : List Bool) : C.wires x = run C.gates x := rfl

theorem run_append (a b : List Gate) (w : List Bool) : run (a ++ b) w = run b (run a w) :=
  List.foldl_append

theorem run_cons (g : Gate) (gs : List Gate) (w : List Bool) : run (g :: gs) w = run gs (step w g) := rfl

theorem run_nil (w : List Bool) : run [] w = w := rfl

theorem run_length (gs : List Gate) (w : List Bool) : (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih => rw [run_cons, ih]; simp [step]; omega

theorem getD_keep (w t : List Bool) {i : ℕ} (hi : i < w.length) :
    (w ++ t).getD i false = w.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem getD_new (w : List Bool) (v : Bool) {i : ℕ} (hi : i = w.length) :
    (w ++ [v]).getD i false = v := by
  subst hi
  simp [List.getD_eq_getElem?_getD]

theorem prefix_keep (gs : List Gate) (w : List Bool) {i : ℕ} (hi : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp [step]; omega)]
    exact getD_keep _ _ hi

def value (C : Circuit) (x : List Bool) (i : ℕ) := (C.wires x).getD i false

theorem value_gate (C : Circuit) (x : List Bool) (j : ℕ) (hj : j < C.gates.length) :
    value C x (x.length + j) =
      (C.gates[j]).op.eval
        ((C.gates[j]).inputs.map fun i => if i < x.length + j then value C x i else false) := by
  let gs := C.gates
  let w := run (gs.take j) x
  have hlen : w.length = x.length + j := by
    simp only [w, run_length, gs, List.length_take, Nat.min_eq_left hj.le]
  have hs : gs = gs.take j ++ gs[j] :: gs.drop (j + 1) := by
    simp [gs, List.take_append_drop]
  have hrun : C.wires x = run (gs.drop (j + 1)) (step w gs[j]) := by
    change run gs x = _
    conv_lhs => rw [hs, run_append, run_cons]
  have hread (i : ℕ) (hi : i < w.length) : value C x i = w.getD i false := by
    change (run gs x).getD i false = _
    conv_lhs => rw [← List.take_append_drop j gs, run_append]
    exact prefix_keep _ _ hi
  unfold value
  conv_lhs => rw [hrun]
  rw [prefix_keep _ _ (by simp [step, hlen])]
  rw [← hlen]
  simp only [step]
  rw [getD_new _ _ rfl]
  apply congrArg _
  apply List.map_congr_left
  intro i _
  split
  · rename_i hi
    exact (hread i hi).symm
  · rename_i hi
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none_iff.2 (by omega : w.length ≤ i)]

section tree

variable (C : Circuit) (n : ℕ)

def gateAt (w : ℕ) : Gate := C.gates.getD (w - n) ⟨GateOp.and, []⟩

def isNot (w : ℕ) : Prop := n ≤ w ∧ (gateAt C n w).op = GateOp.not

open Classical in
noncomputable def reads (w : ℕ) : List ℕ :=
  if (gateAt C n w).op = GateOp.not then (gateAt C n w).inputs.take 1 else (gateAt C n w).inputs

noncomputable def ch (w : ℕ) : List ℕ :=
  if n ≤ w ∧ w - n < C.gates.length then (reads C n w).filter (fun c => decide (c < w)) else []

theorem ch_lt {w c : ℕ} (h : c ∈ ch C n w) : c < w := by
  unfold ch at h
  split at h
  · simpa using (List.mem_filter.1 h).2
  · simp at h

theorem ch_ge {w c : ℕ} (h : c ∈ ch C n w) : n ≤ w := by
  unfold ch at h
  split at h
  · rename_i h'
    exact h'.1
  · simp at h

noncomputable def desc (w : ℕ) : Finset ℕ :=
  insert w ((ch C n w).toFinset.attach.biUnion fun c => desc c.1)
termination_by w
decreasing_by exact ch_lt C n (List.mem_toFinset.mp c.2)

theorem mem_desc (w v : ℕ) : v ∈ desc C n w ↔ v = w ∨ ∃ c ∈ ch C n w, v ∈ desc C n c := by
  conv_lhs => rw [desc]
  simp only [Finset.mem_insert, Finset.mem_biUnion, Finset.mem_attach, true_and, Subtype.exists,
    List.mem_toFinset, exists_prop]

theorem self_desc (w : ℕ) : w ∈ desc C n w := (mem_desc C n w w).2 (Or.inl rfl)

theorem desc_le : ∀ w v, v ∈ desc C n w → v ≤ w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro v hv
    rcases (mem_desc C n w v).1 hv with rfl | ⟨c, hc, h⟩
    · exact le_rfl
    · exact (ih c (ch_lt C n hc) v h).trans (ch_lt C n hc).le

theorem desc_trans : ∀ w v, v ∈ desc C n w → desc C n v ⊆ desc C n w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro v hv
    rcases (mem_desc C n w v).1 hv with rfl | ⟨c, hc, h⟩
    · exact Finset.Subset.refl _
    · intro u hu
      exact (mem_desc C n w u).2 (Or.inr ⟨c, hc, ih c (ch_lt C n hc) v h hu⟩)

theorem desc_parent : ∀ w v, v ∈ desc C n w → v ≠ w → ∃ p ∈ desc C n w, v ∈ ch C n p := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro v hv hne
    rcases (mem_desc C n w v).1 hv with rfl | ⟨c, hc, h⟩
    · exact absurd rfl hne
    · by_cases hvc : v = c
      · exact ⟨w, self_desc C n w, hvc ▸ hc⟩
      · obtain ⟨p, hp, hvp⟩ := ih c (ch_lt C n hc) v h hvc
        exact ⟨p, (mem_desc C n w p).2 (Or.inr ⟨c, hc, hp⟩), hvp⟩

theorem child_desc {o p c : ℕ} (hp : p ∈ desc C n o) (hc : c ∈ ch C n p) : c ∈ desc C n o :=
  desc_trans C n o p hp ((mem_desc C n p c).2 (Or.inr ⟨c, hc, self_desc C n c⟩))

def GoodC : Prop := ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2

theorem gateAt_eq {w : ℕ} (h : w - n < C.gates.length) : gateAt C n w = C.gates[w - n] := by
  unfold gateAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

open Classical in
noncomputable def bnd (w : ℕ) : ℕ := if isNot C n w then 1 else 2

theorem ch_len (hg : GoodC C) {w : ℕ} (hw : n ≤ w) : (ch C n w).length ≤ bnd C n w := by
  classical
  unfold ch bnd
  split
  · rename_i h
    refine (List.length_filter_le _ _).trans ?_
    unfold reads
    have hg' : (gateAt C n w).inputs.length ≤ 2 := by
      rw [gateAt_eq C n h.2]
      exact (hg _ (List.getElem_mem h.2)).2
    by_cases hn : (gateAt C n w).op = GateOp.not
    · rw [if_pos hn, if_pos (show isNot C n w from ⟨hw, hn⟩), List.length_take]
      omega
    · rw [if_neg hn, if_neg (show ¬ isNot C n w from fun c => hn c.2)]
      exact hg'
  · simp

noncomputable def gatesIn (o : ℕ) : Finset ℕ := (desc C n o).filter (fun w => n ≤ w)
noncomputable def leaves (o : ℕ) : Finset ℕ := (desc C n o).filter (fun w => w < n)
open Classical in
noncomputable def nots (o : ℕ) : Finset ℕ := (desc C n o).filter (fun w => isNot C n w)

open Classical in
theorem sum_bnd (o : ℕ) : ∑ p ∈ gatesIn C n o, bnd C n p + (nots C n o).card = 2 * (gatesIn C n o).card := by
  have h1 : nots C n o = (gatesIn C n o).filter (fun w => isNot C n w) := by
    unfold nots gatesIn
    rw [Finset.filter_filter]
    apply Finset.filter_congr
    intro w _
    exact ⟨fun h => ⟨h.1, h⟩, fun h => h.2⟩
  rw [h1, Finset.card_filter, ← Finset.sum_add_distrib, mul_comm, ← smul_eq_mul, ← Finset.sum_const]
  apply Finset.sum_congr rfl
  intro p _
  unfold bnd
  split <;> rfl

theorem leaves_gates (o : ℕ) : (leaves C n o).card + (gatesIn C n o).card = (desc C n o).card := by
  unfold leaves gatesIn
  have := Finset.card_filter_add_card_filter_not (s := desc C n o) (fun w => w < n)
  simpa only [not_lt] using this

theorem parent_cover (o : ℕ) : (desc C n o).erase o ⊆ (gatesIn C n o).biUnion (fun p => (ch C n p).toFinset) := by
  intro v hv
  rw [Finset.mem_erase] at hv
  obtain ⟨p, hp, hvp⟩ := desc_parent C n o v hv.2 hv.1
  rw [Finset.mem_biUnion]
  exact ⟨p, Finset.mem_filter.2 ⟨hp, ch_ge C n hvp⟩, List.mem_toFinset.2 hvp⟩

theorem card_ch_le (hg : GoodC C) (o p : ℕ) (hp : p ∈ gatesIn C n o) : (ch C n p).toFinset.card ≤ bnd C n p :=
  (List.toFinset_card_le _).trans (ch_len C n hg (Finset.mem_filter.1 hp).2)

theorem count (hg : GoodC C) (o : ℕ) : (leaves C n o).card + (nots C n o).card ≤ (gatesIn C n o).card + 1 := by
  have h1 := Finset.card_le_card (parent_cover C n o)
  rw [Finset.card_erase_of_mem (self_desc C n o)] at h1
  have h2 : ((gatesIn C n o).biUnion (fun p => (ch C n p).toFinset)).card ≤
      ∑ p ∈ gatesIn C n o, (ch C n p).toFinset.card := Finset.card_biUnion_le
  have h3 := Finset.sum_le_sum (card_ch_le C n hg o)
  have h4 := sum_bnd C n o
  have h5 := leaves_gates C n o
  omega

theorem exact_count (hg : GoodC C) (o : ℕ)
    (hex : (gatesIn C n o).card + 1 ≤ (leaves C n o).card + (nots C n o).card) :
    (∀ p ∈ gatesIn C n o, (ch C n p).toFinset.card = bnd C n p) ∧
    (∀ p ∈ desc C n o, ∀ r ∈ desc C n o, ∀ c, c ∈ ch C n p → c ∈ ch C n r → p = r) := by
  have h1 := Finset.card_le_card (parent_cover C n o)
  rw [Finset.card_erase_of_mem (self_desc C n o)] at h1
  have h2 : ((gatesIn C n o).biUnion (fun p => (ch C n p).toFinset)).card ≤
      ∑ p ∈ gatesIn C n o, (ch C n p).toFinset.card := Finset.card_biUnion_le
  have h3 := Finset.sum_le_sum (card_ch_le C n hg o)
  have h4 := sum_bnd C n o
  have h5 := leaves_gates C n o
  have h6 : ∑ p ∈ gatesIn C n o, (ch C n p).toFinset.card = ∑ p ∈ gatesIn C n o, bnd C n p := by omega
  have h7 : ∑ p ∈ gatesIn C n o, (ch C n p).toFinset.card ≤
      ((gatesIn C n o).biUnion (fun p => (ch C n p).toFinset)).card := by omega
  refine ⟨(Finset.sum_eq_sum_iff_of_le (card_ch_le C n hg o)).1 h6, ?_⟩
  intro p hp r hr c hcp hcr
  by_contra hpr
  have hpG : p ∈ gatesIn C n o := Finset.mem_filter.2 ⟨hp, ch_ge C n hcp⟩
  have hrG : r ∈ gatesIn C n o := Finset.mem_filter.2 ⟨hr, ch_ge C n hcr⟩
  let F : ℕ → Finset ℕ := fun s => if s = r then (ch C n s).toFinset.erase c else (ch C n s).toFinset
  have hsub : (gatesIn C n o).biUnion (fun p => (ch C n p).toFinset) ⊆ (gatesIn C n o).biUnion F := by
    intro v hv
    rw [Finset.mem_biUnion] at hv ⊢
    obtain ⟨s, hs, hvs⟩ := hv
    by_cases hvc : v = c
    · refine ⟨p, hpG, ?_⟩
      simp only [F, if_neg hpr, hvc]
      exact List.mem_toFinset.2 hcp
    · refine ⟨s, hs, ?_⟩
      simp only [F]
      split
      · exact Finset.mem_erase.2 ⟨hvc, hvs⟩
      · exact hvs
  have h8 : ∑ s ∈ gatesIn C n o, (F s).card < ∑ s ∈ gatesIn C n o, (ch C n s).toFinset.card := by
    apply Finset.sum_lt_sum
    · intro s _
      simp only [F]
      split
      · exact Finset.card_erase_le
      · exact le_rfl
    · refine ⟨r, hrG, ?_⟩
      simp only [F, if_true]
      exact Finset.card_erase_lt_of_mem (List.mem_toFinset.2 hcr)
  have h9 := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  omega

theorem sib_disj (o : ℕ)
    (huniq : ∀ p ∈ desc C n o, ∀ r ∈ desc C n o, ∀ c, c ∈ ch C n p → c ∈ ch C n r → p = r)
    (p a b : ℕ) (hp : p ∈ desc C n o) (ha : a ∈ ch C n p) (hb : b ∈ ch C n p) (hab : a ≠ b) :
    Disjoint (desc C n a) (desc C n b) := by
  have haT := child_desc C n hp ha
  have hbT := child_desc C n hp hb
  have top : ∀ a b : ℕ, a ∈ ch C n p → b ∈ ch C n p → a ≠ b → a ∈ desc C n o → b ∈ desc C n o →
      a ∈ desc C n b → False := by
    intro a b ha hb hab haT hbT h
    obtain ⟨r, hr, har⟩ := desc_parent C n b a h hab
    have hrT := desc_trans C n o b hbT hr
    have : p = r := huniq p hp r hrT a ha har
    have := desc_le C n b r hr
    have := ch_lt C n hb
    omega
  have main : ∀ d v, p - v = d → v ∈ desc C n a → v ∈ desc C n b → False := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro v hd hva hvb
      by_cases h1 : v = a
      · exact top a b ha hb hab haT hbT (h1 ▸ hvb)
      by_cases h2 : v = b
      · exact top b a hb ha hab.symm hbT haT (h2 ▸ hva)
      obtain ⟨s, hs, hvs⟩ := desc_parent C n a v hva h1
      obtain ⟨r, hr, hvr⟩ := desc_parent C n b v hvb h2
      have hsr : s = r := huniq s (desc_trans C n o a haT hs) r (desc_trans C n o b hbT hr) v hvs hvr
      subst hsr
      have h3 := desc_le C n a s hs
      have h4 := ch_lt C n ha
      have h5 := ch_lt C n hvs
      exact ih (p - s) (by omega) s rfl hs hr
  rw [Finset.disjoint_left]
  intro v hva hvb
  exact main _ v rfl hva hvb

end tree

def Node (n : ℕ) (T : Finset ℕ) (V : ℕ → (ℕ → Bool) → Bool) (S : ℕ → Finset ℕ) (N : ℕ → Prop) (w : ℕ) : Prop :=
  (w < n ∧ S w = {w} ∧ ∀ f, V w f = f w) ∨
  (n ≤ w ∧ ¬ N w ∧ ∃ a ∈ T, ∃ b ∈ T, a < w ∧ b < w ∧ Disjoint (S a) (S b) ∧ S w = insert w (S a ∪ S b) ∧
    ((∀ f, V w f = (V a f && V b f)) ∨ ∀ f, V w f = (V a f || V b f))) ∨
  (n ≤ w ∧ N w ∧ ∃ a ∈ T, a < w ∧ S w = insert w (S a) ∧ ∀ f, V w f = !V a f)

def inp (n : ℕ) (f : ℕ → Bool) : List Bool := (List.range n).map f

theorem tree_nodes (C : Circuit) (n : ℕ) (hg : GoodC C) (o : ℕ) (ho : o < n + C.gates.length)
    (hex : (gatesIn C n o).card + 1 ≤ (leaves C n o).card + (nots C n o).card) :
    ∀ w ∈ desc C n o, Node n (desc C n o) (fun w f => value C (inp n f) w) (desc C n) (isNot C n) w := by
  classical
  intro w hw
  obtain ⟨hcard, huniq⟩ := exact_count C n hg o hex
  have hlen : ∀ f, (inp n f).length = n := fun f => by simp [inp]
  by_cases hwn : w < n
  · refine Or.inl ⟨hwn, ?_, ?_⟩
    · ext v
      rw [mem_desc]
      have : ch C n w = [] := by
        unfold ch
        rw [if_neg (by omega)]
      simp [this]
    · intro f
      change (run C.gates (inp n f)).getD w false = f w
      rw [prefix_keep _ _ (by rw [hlen]; exact hwn)]
      simp [inp, List.getD_eq_getElem?_getD, hwn]
  have hwn' : n ≤ w := by omega
  right
  have hwo := desc_le C n o w hw
  have hj : w - n < C.gates.length := by omega
  have hnw : n + (w - n) = w := by omega
  have hval : ∀ f, value C (inp n f) w = (gateAt C n w).op.eval
      ((gateAt C n w).inputs.map fun i => if i < w then value C (inp n f) i else false) := by
    intro f
    have := value_gate C (inp n f) (w - n) hj
    rw [hlen, hnw] at this
    rw [gateAt_eq C n hj]
    exact this
  have hG : w ∈ gatesIn C n o := Finset.mem_filter.2 ⟨hw, hwn'⟩
  have hc := hcard w hG
  have hch : ch C n w = (reads C n w).filter (fun c => decide (c < w)) := by
    unfold ch
    rw [if_pos ⟨hwn', hj⟩]
  have hop := hg _ (List.getElem_mem hj)
  rw [← gateAt_eq C n hj] at hop
  have hdesc : ∀ v, v ∈ desc C n w ↔ v = w ∨ ∃ c ∈ ch C n w, v ∈ desc C n c := mem_desc C n w
  have hlenle : (ch C n w).toFinset.card ≤ (ch C n w).length := List.toFinset_card_le _
  by_cases hN : isNot C n w
  · right
    refine ⟨hwn', hN, ?_⟩
    have hop' : (gateAt C n w).op = GateOp.not := hN.2
    have hreads : reads C n w = (gateAt C n w).inputs.take 1 := by
      unfold reads
      rw [if_pos hop']
    rw [show bnd C n w = 1 from if_pos hN] at hc
    cases hin : (gateAt C n w).inputs with
    | nil =>
      rw [hin] at hreads
      rw [hch, hreads] at hc
      simp at hc
    | cons a l =>
      rw [hin] at hreads
      simp only [List.take_succ_cons, List.take_zero] at hreads
      have haw : a < w := by
        by_contra h
        rw [hch, hreads] at hc
        simp [h] at hc
      have hcha : ch C n w = [a] := by
        rw [hch, hreads]
        simp [haw]
      have haT : a ∈ desc C n o := child_desc C n hw (hcha ▸ List.mem_singleton_self a)
      refine ⟨a, haT, haw, ?_, ?_⟩
      · ext v
        rw [hdesc, hcha]
        simp
      · intro f
        change value C (inp n f) w = !value C (inp n f) a
        rw [hval, hop', hin]
        simp [GateOp.eval, haw]
  · left
    refine ⟨hwn', hN, ?_⟩
    have hop' : (gateAt C n w).op ≠ GateOp.not := fun c => hN ⟨hwn', c⟩
    have hreads : reads C n w = (gateAt C n w).inputs := by
      unfold reads
      rw [if_neg hop']
    rw [show bnd C n w = 2 from if_neg hN] at hc
    have h2 := hop.2
    have hfl := List.length_filter_le (fun c => decide (c < w)) (gateAt C n w).inputs
    rw [hch, hreads] at hlenle hc
    have hlen2 : (gateAt C n w).inputs.length = 2 := by omega
    obtain ⟨a, b, hab⟩ := List.length_eq_two.1 hlen2
    rw [hab] at hlenle hc hfl
    have haw : a < w := by
      by_contra h
      by_cases h' : b < w <;> simp [h, h'] at hc
    have hbw : b < w := by
      by_contra h
      simp [haw, h] at hc
    have hne : a ≠ b := by
      intro h
      subst h
      simp [haw] at hc
    have hchab : ch C n w = [a, b] := by
      rw [hch, hreads, hab]
      simp [haw, hbw]
    have haT : a ∈ desc C n o := child_desc C n hw (by rw [hchab]; simp)
    have hbT : b ∈ desc C n o := child_desc C n hw (by rw [hchab]; simp)
    refine ⟨a, haT, b, hbT, haw, hbw, ?_, ?_, ?_⟩
    · exact sib_disj C n o huniq w a b hw (by rw [hchab]; simp) (by rw [hchab]; simp) hne
    · ext v
      rw [hdesc, hchab]
      simp
    · rcases hop.1 with h | h | h
      · left
        intro f
        change value C (inp n f) w = (value C (inp n f) a && value C (inp n f) b)
        rw [hval, h, hab]
        simp [GateOp.eval, haw, hbw]
      · right
        intro f
        change value C (inp n f) w = (value C (inp n f) a || value C (inp n f) b)
        rw [hval, h, hab]
        simp [GateOp.eval, haw, hbw]
      · exact absurd h hop'

def only (z : ℕ) : ℕ → Bool := fun i => decide (i = z)
def two (a b : ℕ) : ℕ → Bool := fun i => decide (i = a ∨ i = b)
def zero : ℕ → Bool := fun _ => false

section nodes

variable {n : ℕ} {T : Finset ℕ} {V : ℕ → (ℕ → Bool) → Bool} {S : ℕ → Finset ℕ} {N : ℕ → Prop}
  (H : ∀ w ∈ T, Node n T V S N w)

def sup (n : ℕ) (S : ℕ → Finset ℕ) (w : ℕ) : Finset ℕ := (S w).filter (fun i => i < n)

theorem sup_bin {a b w : ℕ} (h : S w = insert w (S a ∪ S b)) (hw : n ≤ w) (i : ℕ) :
    i ∈ sup n S w ↔ i ∈ sup n S a ∨ i ∈ sup n S b := by
  unfold sup
  rw [h, Finset.filter_insert, if_neg (by omega), Finset.filter_union, Finset.mem_union]

theorem sup_un {a w : ℕ} (h : S w = insert w (S a)) (hw : n ≤ w) : sup n S w = sup n S a := by
  unfold sup
  rw [h, Finset.filter_insert, if_neg (by omega)]

theorem sup_leaf {w : ℕ} (h : S w = {w}) (hw : w < n) : sup n S w = {w} := by
  unfold sup
  rw [h, Finset.filter_singleton, if_pos hw]

theorem sup_disj {a b : ℕ} (h : Disjoint (S a) (S b)) {i : ℕ} (ha : i ∈ sup n S a) (hb : i ∈ sup n S b) : False :=
  Finset.disjoint_left.1 h (Finset.mem_filter.1 ha).1 (Finset.mem_filter.1 hb).1

include H

theorem self_mem : ∀ w ∈ T, w ∈ S w := by
  intro w hw
  rcases H w hw with ⟨_, h, _⟩ | ⟨_, _, a, _, b, _, _, _, _, h, _⟩ | ⟨_, _, a, _, _, h, _⟩
  · rw [h]
    exact Finset.mem_singleton_self _
  · rw [h]
    exact Finset.mem_insert_self _ _
  · rw [h]
    exact Finset.mem_insert_self _ _

theorem sup_ne : ∀ w ∈ T, (sup n S w).Nonempty := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    rcases H w hw with ⟨h1, h2, _⟩ | ⟨h0, _, a, ha, b, _, haw, _, _, h, _⟩ | ⟨h0, _, a, ha, haw, h, _⟩
    · rw [sup_leaf h2 h1]
      exact Finset.singleton_nonempty _
    · obtain ⟨i, hi⟩ := ih a haw ha
      exact ⟨i, (sup_bin h h0 i).2 (Or.inl hi)⟩
    · rw [sup_un h h0]
      exact ih a haw ha

theorem dep : ∀ w ∈ T, ∀ f g : ℕ → Bool, (∀ i ∈ sup n S w, f i = g i) → V w f = V w g := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw f g hfg
    rcases H w hw with ⟨h1, h2, h3⟩ | ⟨h0, _, a, ha, b, hb, haw, hbw, _, h, hv⟩ | ⟨h0, _, a, ha, haw, h, hv⟩
    · rw [h3, h3]
      exact hfg w (by rw [sup_leaf h2 h1]; simp)
    · have e1 := ih a haw ha f g (fun i hi => hfg i ((sup_bin h h0 i).2 (Or.inl hi)))
      have e2 := ih b hbw hb f g (fun i hi => hfg i ((sup_bin h h0 i).2 (Or.inr hi)))
      rcases hv with hv | hv <;> rw [hv, hv, e1, e2]
    · rw [hv, hv, ih a haw ha f g (fun i hi => hfg i (by rw [sup_un h h0]; exact hi))]

theorem mono : ∀ w ∈ T, (∀ v ∈ S w, ¬ N v) → ∀ f g : ℕ → Bool, (∀ i, f i = true → g i = true) →
    V w f = true → V w g = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hm f g hfg
    rcases H w hw with ⟨_, _, h3⟩ | ⟨_, _, a, ha, b, hb, haw, hbw, _, h, hv⟩ | ⟨_, hN, _⟩
    · rw [h3, h3]
      exact hfg w
    · have ma := ih a haw ha (fun v hv => hm v (by rw [h]; simp [hv])) f g hfg
      have mb := ih b hbw hb (fun v hv => hm v (by rw [h]; simp [hv])) f g hfg
      rcases hv with hv | hv <;> rw [hv, hv]
      · simp only [Bool.and_eq_true]
        exact fun p => ⟨ma p.1, mb p.2⟩
      · simp only [Bool.or_eq_true]
        exact fun p => p.imp ma mb
    · exact absurd hN (hm w (self_mem H w hw))

theorem mono_zero : ∀ w ∈ T, (∀ v ∈ S w, ¬ N v) → V w zero = false := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hm
    rcases H w hw with ⟨_, _, h3⟩ | ⟨_, _, a, ha, b, hb, haw, hbw, _, h, hv⟩ | ⟨_, hN, _⟩
    · rw [h3]
      rfl
    · have ma := ih a haw ha (fun v hv => hm v (by rw [h]; simp [hv]))
      have mb := ih b hbw hb (fun v hv => hm v (by rw [h]; simp [hv]))
      rcases hv with hv | hv <;> rw [hv, ma, mb] <;> rfl
    · exact absurd hN (hm w (self_mem H w hw))

theorem off {w : ℕ} (hw : w ∈ T) (hm : ∀ v ∈ S w, ¬ N v) (f : ℕ → Bool)
    (hf : ∀ i ∈ sup n S w, f i = false) : V w f = false :=
  (dep H w hw f zero hf).trans (mono_zero H w hw hm)

theorem in_sup {w : ℕ} (hw : w ∈ T) (a b : ℕ) (h1 : V w (two a b) = true) (h2 : V w (only b) = false) :
    a ∈ sup n S w := by
  by_contra h
  have : V w (two a b) = V w (only b) := by
    apply dep H w hw
    intro i hi
    have : i ≠ a := fun c => h (c ▸ hi)
    simp [two, only, this]
  rw [this, h2] at h1
  exact Bool.false_ne_true h1

end nodes

def Pr {k : ℕ} (xi yi : Fin k → ℕ) (s : Finset (Fin k)) (M : Finset (Finset (Fin k))) (f : ℕ → Bool) : Prop :=
  (∃ u ∈ s, f (xi u) = true ∧ f (yi u) = true) ∨
  ∃ e ∈ M, (∀ u ∈ e, f (xi u) = true) ∨ (∀ u ∈ e, f (yi u) = true)

theorem Pr_union {k : ℕ} (xi yi : Fin k → ℕ) (s t : Finset (Fin k)) (M L : Finset (Finset (Fin k)))
    (f : ℕ → Bool) : Pr xi yi (s ∪ t) (M ∪ L) f ↔ Pr xi yi s M f ∨ Pr xi yi t L f := by
  simp only [Pr, Finset.mem_union, or_and_right, exists_or]
  exact or_or_or_comm

theorem isM_union {k : ℕ} (s t : Finset (Fin k)) (M L : Finset (Finset (Fin k))) (hM : IsM M) (hL : IsM L)
    (hs : ∀ e ∈ M, e ⊆ s) (ht : ∀ e ∈ L, e ⊆ t) (hd : Disjoint s t) :
    IsM (M ∪ L) ∧ ∀ e ∈ M ∪ L, e ⊆ s ∪ t := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro e he
    rcases Finset.mem_union.1 he with h | h
    · exact hM.1 e h
    · exact hL.1 e h
  · intro e he g hg hne
    rcases Finset.mem_union.1 he with h | h <;> rcases Finset.mem_union.1 hg with h' | h'
    · exact hM.2 e h g h' hne
    · exact hd.mono (hs e h) (ht g h')
    · exact (hd.mono (hs g h') (ht e h)).symm
    · exact hL.2 e h g h' hne
  · intro e he
    rcases Finset.mem_union.1 he with h | h
    · exact (hs e h).trans Finset.subset_union_left
    · exact (ht e h).trans Finset.subset_union_right

section classify

variable {n : ℕ} {T : Finset ℕ} {V : ℕ → (ℕ → Bool) → Bool} {S : ℕ → Finset ℕ} {N : ℕ → Prop}
  (H : ∀ w ∈ T, Node n T V S N w) {k : ℕ} (xi yi : Fin k → ℕ)
  (hx : ∀ u v, xi u = xi v → u = v) (hy : ∀ u v, yi u = yi v → u = v) (hxy : ∀ u v, xi u ≠ yi v)

include H

theorem and_child {a : ℕ} (ha : a ∈ T) (ma : ∀ v ∈ S a, ¬ N v) (f : ℕ → Bool)
    (h1 : ∀ z ∈ sup n S a, V a (only z) = true) : V a f = true ↔ ∃ z ∈ sup n S a, f z = true := by
  constructor
  · intro h
    by_contra c
    have : V a f = false := off H ha ma f (fun i hi => by
      cases hfi : f i
      · rfl
      · exact absurd ⟨i, hi, hfi⟩ c)
    rw [this] at h
    exact Bool.false_ne_true h
  · rintro ⟨z, hz, hfz⟩
    apply mono H a ha ma (only z) f _ (h1 z hz)
    intro i hi
    simp only [only, decide_eq_true_eq] at hi
    rw [hi]
    exact hfz

include hx hy hxy

theorem cls_id : ∀ w ∈ T, (∀ v ∈ S w, ¬ N v) → ∀ s : Finset (Fin k),
    (∀ i, i ∈ sup n S w ↔ ∃ u ∈ s, i = xi u ∨ i = yi u) →
    (∀ u ∈ s, ∀ v ∈ s, V w (two (xi u) (yi v)) = decide (u = v)) →
    (∀ z, V w (only z) = false) →
    ∃ M : Finset (Finset (Fin k)), IsM M ∧ (∀ e ∈ M, e ⊆ s) ∧ ∀ f, (V w f = true ↔ Pr xi yi s M f) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hm s hs hval hsing
    rcases H w hw with ⟨h1, h2, _⟩ | ⟨h0, _, a, ha, b, hb, haw, hbw, hd, h, hv⟩ | ⟨_, hN, _⟩
    · exfalso
      obtain ⟨i, hi⟩ := sup_ne H w hw
      obtain ⟨u, hu, _⟩ := (hs i).1 hi
      have e1 : xi u ∈ sup n S w := (hs _).2 ⟨u, hu, Or.inl rfl⟩
      have e2 : yi u ∈ sup n S w := (hs _).2 ⟨u, hu, Or.inr rfl⟩
      rw [sup_leaf h2 h1, Finset.mem_singleton] at e1 e2
      exact hxy u u (e1.trans e2.symm)
    swap
    · exact absurd hN (hm w (self_mem H w hw))
    have ma : ∀ v ∈ S a, ¬ N v := fun v hv => hm v (by rw [h]; simp [hv])
    have mb : ∀ v ∈ S b, ¬ N v := fun v hv => hm v (by rw [h]; simp [hv])
    have hsup := sup_bin (n := n) h h0
    have disj : ∀ i, i ∈ sup n S a → i ∈ sup n S b → False := fun i => sup_disj hd
    have inab : ∀ u ∈ s, (xi u ∈ sup n S a ∨ xi u ∈ sup n S b) ∧ (yi u ∈ sup n S a ∨ yi u ∈ sup n S b) :=
      fun u hu => ⟨(hsup _).1 ((hs _).2 ⟨u, hu, Or.inl rfl⟩), (hsup _).1 ((hs _).2 ⟨u, hu, Or.inr rfl⟩)⟩
    have offt : ∀ c ∈ T, (∀ v ∈ S c, ¬ N v) → ∀ p q : ℕ, p ∉ sup n S c → q ∉ sup n S c →
        V c (two p q) = false := by
      intro c hc mc p q hp hq
      apply off H hc mc
      intro i hi
      have e1 : i ≠ p := fun e => hp (e ▸ hi)
      have e2 : i ≠ q := fun e => hq (e ▸ hi)
      simp [two, e1, e2]
    have onel : ∀ c ∈ T, ∀ p q : ℕ, q ∉ sup n S c → V c (two p q) = V c (only p) := by
      intro c hc p q hq
      apply dep H c hc
      intro i hi
      have e : i ≠ q := fun e => hq (e ▸ hi)
      simp [two, only, e]
    have oner : ∀ c ∈ T, ∀ p q : ℕ, p ∉ sup n S c → V c (two p q) = V c (only q) := by
      intro c hc p q hp
      apply dep H c hc
      intro i hi
      have e : i ≠ p := fun e => hp (e ▸ hi)
      simp [two, only, e]
    rcases hv with hv | hv
    · have h1 : ∀ u ∈ s, V a (two (xi u) (yi u)) = true ∧ V b (two (xi u) (yi u)) = true := by
        intro u hu
        have := hval u hu u hu
        rw [hv] at this
        simpa using this
      have h2 : ∀ u ∈ s, (xi u ∈ sup n S a ∨ yi u ∈ sup n S a) ∧ (xi u ∈ sup n S b ∨ yi u ∈ sup n S b) := by
        intro u hu
        constructor
        · by_contra c
          rw [not_or] at c
          have := offt a ha ma _ _ c.1 c.2
          rw [(h1 u hu).1] at this
          exact Bool.noConfusion this
        · by_contra c
          rw [not_or] at c
          have := offt b hb mb _ _ c.1 c.2
          rw [(h1 u hu).2] at this
          exact Bool.noConfusion this
      have h3a : ∀ z ∈ sup n S a, V a (only z) = true := by
        intro z hz
        obtain ⟨u, hu, rfl | rfl⟩ := (hs z).1 ((hsup z).2 (Or.inl hz))
        · have : yi u ∉ sup n S a := by
            intro c
            rcases (h2 u hu).2 with d | d
            · exact disj _ hz d
            · exact disj _ c d
          rw [← onel a ha (xi u) (yi u) this]
          exact (h1 u hu).1
        · have : xi u ∉ sup n S a := by
            intro c
            rcases (h2 u hu).2 with d | d
            · exact disj _ c d
            · exact disj _ hz d
          rw [← oner a ha (xi u) (yi u) this]
          exact (h1 u hu).1
      have h3b : ∀ z ∈ sup n S b, V b (only z) = true := by
        intro z hz
        obtain ⟨u, hu, rfl | rfl⟩ := (hs z).1 ((hsup z).2 (Or.inr hz))
        · have : yi u ∉ sup n S b := by
            intro c
            rcases (h2 u hu).1 with d | d
            · exact disj _ d hz
            · exact disj _ d c
          rw [← onel b hb (xi u) (yi u) this]
          exact (h1 u hu).2
        · have : xi u ∉ sup n S b := by
            intro c
            rcases (h2 u hu).1 with d | d
            · exact disj _ d c
            · exact disj _ d hz
          rw [← oner b hb (xi u) (yi u) this]
          exact (h1 u hu).2
      have core : ∀ a ∈ T, ∀ b ∈ T, (∀ v ∈ S a, ¬ N v) → (∀ v ∈ S b, ¬ N v) →
          (∀ i, i ∈ sup n S w ↔ i ∈ sup n S a ∨ i ∈ sup n S b) →
          (∀ i, i ∈ sup n S a → i ∈ sup n S b → False) →
          (∀ z ∈ sup n S a, V a (only z) = true) → (∀ z ∈ sup n S b, V b (only z) = true) →
          (∀ f, V w f = (V a f && V b f)) →
          ∀ p ∈ s, ∀ q ∈ s, q ≠ p → xi p ∈ sup n S a →
          ∃ M : Finset (Finset (Fin k)), IsM M ∧ (∀ e ∈ M, e ⊆ s) ∧ ∀ f, (V w f = true ↔ Pr xi yi s M f) := by
        intro a ha b hb ma mb hsup disj h3a h3b hv p hp q hq hqp hpa
        have cross : ∀ u ∈ s, ∀ v ∈ s, u ≠ v → xi u ∈ sup n S a → yi v ∈ sup n S b → False := by
          intro u hu v hv' huv h1 h2
          have e1 : V a (two (xi u) (yi v)) = true :=
            (and_child H ha ma _ h3a).2 ⟨_, h1, by simp [two]⟩
          have e2 : V b (two (xi u) (yi v)) = true :=
            (and_child H hb mb _ h3b).2 ⟨_, h2, by simp [two]⟩
          have := hval u hu v hv'
          rw [hv, e1, e2] at this
          simp [huv] at this
        have cross' : ∀ u ∈ s, ∀ v ∈ s, u ≠ v → xi u ∈ sup n S b → yi v ∈ sup n S a → False := by
          intro u hu v hv' huv h1 h2
          have e1 : V a (two (xi u) (yi v)) = true :=
            (and_child H ha ma _ h3a).2 ⟨_, h2, by simp [two]⟩
          have e2 : V b (two (xi u) (yi v)) = true :=
            (and_child H hb mb _ h3b).2 ⟨_, h1, by simp [two]⟩
          have := hval u hu v hv'
          rw [hv, e1, e2] at this
          simp [huv] at this
        have mem : ∀ u ∈ s, ∀ z, (z = xi u ∨ z = yi u) → z ∈ sup n S a ∨ z ∈ sup n S b := by
          intro u hu z hz
          exact (hsup z).1 ((hs z).2 ⟨u, hu, hz⟩)
        have yqa : yi q ∈ sup n S a :=
          (mem q hq _ (Or.inr rfl)).resolve_right (fun c => cross p hp q hq hqp.symm hpa c)
        have xqb : xi q ∈ sup n S b := by
          refine (mem q hq _ (Or.inl rfl)).resolve_left (fun c => ?_)
          have : V b (two (xi q) (yi q)) = false := by
            apply off H hb mb
            intro i hi
            have e1 : i ≠ xi q := fun e => disj _ c (e ▸ hi)
            have e2 : i ≠ yi q := fun e => disj _ yqa (e ▸ hi)
            simp [two, e1, e2]
          have h := hval q hq q hq
          rw [hv, this] at h
          simp at h
        have ypb : yi p ∈ sup n S b :=
          (mem p hp _ (Or.inr rfl)).resolve_left (fun c => cross' q hq p hp hqp xqb c)
        have only2 : ∀ r ∈ s, r = p ∨ r = q := by
          intro r hr
          by_contra c
          rw [not_or] at c
          rcases mem r hr (yi r) (Or.inr rfl) with d | d
          · exact cross' q hq r hr (Ne.symm c.2) xqb d
          · exact cross p hp r hr (Ne.symm c.1) hpa d
        have hs2 : s = {p, q} := by
          ext r
          simp only [Finset.mem_insert, Finset.mem_singleton]
          constructor
          · exact only2 r
          · rintro (rfl | rfl) <;> assumption
        have ma' : ∀ z, z ∈ sup n S a ↔ z = xi p ∨ z = yi q := by
          intro z
          constructor
          · intro hz
            obtain ⟨u, hu, e⟩ := (hs z).1 ((hsup z).2 (Or.inl hz))
            rcases only2 u hu with rfl | rfl <;> rcases e with rfl | rfl
            · exact Or.inl rfl
            · exact (disj _ hz ypb).elim
            · exact (disj _ hz xqb).elim
            · exact Or.inr rfl
          · rintro (rfl | rfl) <;> assumption
        have mb' : ∀ z, z ∈ sup n S b ↔ z = xi q ∨ z = yi p := by
          intro z
          constructor
          · intro hz
            obtain ⟨u, hu, e⟩ := (hs z).1 ((hsup z).2 (Or.inr hz))
            rcases only2 u hu with rfl | rfl <;> rcases e with rfl | rfl
            · exact (disj _ hpa hz).elim
            · exact Or.inr rfl
            · exact Or.inl rfl
            · exact (disj _ yqa hz).elim
          · rintro (rfl | rfl) <;> assumption
        refine ⟨{{p, q}}, ⟨?_, ?_⟩, ?_, ?_⟩
        · intro e he
          rw [Finset.mem_singleton] at he
          rw [he, Finset.card_pair hqp.symm]
        · intro e he g hg hne
          rw [Finset.mem_singleton] at he hg
          exact absurd (he.trans hg.symm) hne
        · intro e he
          rw [Finset.mem_singleton] at he
          rw [he, hs2]
        · intro f
          rw [hv, Bool.and_eq_true, and_child H ha ma f h3a, and_child H hb mb f h3b]
          simp only [ma', mb', or_and_right, exists_or, exists_eq_left]
          rw [hs2]
          simp only [Pr, Finset.mem_insert, Finset.mem_singleton, or_and_right, exists_or, exists_eq_left,
            forall_eq_or_imp, forall_eq]
          tauto
      obtain ⟨i, hi⟩ := sup_ne H w hw
      obtain ⟨p, hp, _⟩ := (hs i).1 hi
      by_cases hq : ∃ q ∈ s, q ≠ p
      · obtain ⟨q, hq, hqp⟩ := hq
        rcases (inab p hp).1 with c | c
        · exact core a ha b hb ma mb hsup disj h3a h3b hv p hp q hq hqp c
        · exact core b hb a ha mb ma (fun i => (hsup i).trans or_comm) (fun i x y => disj i y x) h3b h3a
            (fun f => by rw [hv, Bool.and_comm]) p hp q hq hqp c
      · have only1 : ∀ r ∈ s, r = p := fun r hr => by
          by_contra c
          exact hq ⟨r, hr, c⟩
        have hs1 : s = {p} := by
          ext r
          rw [Finset.mem_singleton]
          exact ⟨only1 r, fun e => e ▸ hp⟩
        have vars : ∀ z, z ∈ sup n S w → z = xi p ∨ z = yi p := by
          intro z hz
          obtain ⟨u, hu, e⟩ := (hs z).1 hz
          rwa [only1 u hu] at e
        refine ⟨∅, isM_empty, by simp, ?_⟩
        intro f
        rw [hv, Bool.and_eq_true, and_child H ha ma f h3a, and_child H hb mb f h3b]
        have goal : Pr xi yi s ∅ f ↔ f (xi p) = true ∧ f (yi p) = true := by
          simp [Pr, hs1]
        rw [goal]
        have key : (xi p ∈ sup n S a ∧ yi p ∈ sup n S b) ∨ (yi p ∈ sup n S a ∧ xi p ∈ sup n S b) := by
          rcases (inab p hp).1 with c | c
          · rcases (h2 p hp).2 with d | d
            · exact (disj _ c d).elim
            · exact Or.inl ⟨c, d⟩
          · rcases (h2 p hp).1 with d | d
            · exact (disj _ d c).elim
            · exact Or.inr ⟨d, c⟩
        have uni : ∀ c : ℕ, ∀ z0, z0 ∈ sup n S c → (∀ z ∈ sup n S c, z = z0) →
            ((∃ z ∈ sup n S c, f z = true) ↔ f z0 = true) := by
          intro c z0 h0' hu
          constructor
          · rintro ⟨z, hz, hf⟩
            rwa [hu z hz] at hf
          · intro hf
            exact ⟨z0, h0', hf⟩
        rcases key with ⟨k1, k2⟩ | ⟨k1, k2⟩
        · rw [uni a (xi p) k1, uni b (yi p) k2]
          · intro z hz
            rcases vars z ((hsup z).2 (Or.inr hz)) with e | e
            · exact (disj _ k1 (e ▸ hz)).elim
            · exact e
          · intro z hz
            rcases vars z ((hsup z).2 (Or.inl hz)) with e | e
            · exact e
            · exact (disj _ (e ▸ hz) k2).elim
        · rw [uni a (yi p) k1, uni b (xi p) k2, and_comm]
          · intro z hz
            rcases vars z ((hsup z).2 (Or.inr hz)) with e | e
            · exact e
            · exact (disj _ k1 (e ▸ hz)).elim
          · intro z hz
            rcases vars z ((hsup z).2 (Or.inl hz)) with e | e
            · exact (disj _ (e ▸ hz) k2).elim
            · exact e
    · have sa0 : ∀ z, V a (only z) = false ∧ V b (only z) = false := by
        intro z
        have := hsing z
        rw [hv] at this
        simpa using this
      have tog : ∀ u ∈ s, (xi u ∈ sup n S a ∧ yi u ∈ sup n S a) ∨ (xi u ∈ sup n S b ∧ yi u ∈ sup n S b) := by
        intro u hu
        have tr : V w (two (xi u) (yi u)) = true := by
          rw [hval u hu u hu]
          simp
        rw [hv] at tr
        rcases (inab u hu).1 with c1 | c1 <;> rcases (inab u hu).2 with c2 | c2
        · exact Or.inl ⟨c1, c2⟩
        · rw [onel a ha _ _ (fun c => disj _ c c2), oner b hb _ _ (fun c => disj _ c1 c),
            (sa0 _).1, (sa0 _).2] at tr
          exact Bool.noConfusion tr
        · rw [oner a ha _ _ (fun c => disj _ c c1), onel b hb _ _ (fun c => disj _ c2 c),
            (sa0 _).1, (sa0 _).2] at tr
          exact Bool.noConfusion tr
        · exact Or.inr ⟨c1, c2⟩
      have part : ∀ a ∈ T, ∀ b ∈ T, a < w → (∀ v ∈ S a, ¬ N v) → (∀ v ∈ S b, ¬ N v) →
          (∀ i, i ∈ sup n S w ↔ i ∈ sup n S a ∨ i ∈ sup n S b) →
          (∀ i, i ∈ sup n S a → i ∈ sup n S b → False) →
          (∀ f, V w f = (V a f || V b f)) →
          (∀ u ∈ s, (xi u ∈ sup n S a ∧ yi u ∈ sup n S a) ∨ (xi u ∈ sup n S b ∧ yi u ∈ sup n S b)) →
          ∃ M : Finset (Finset (Fin k)), IsM M ∧ (∀ e ∈ M, e ⊆ s.filter (fun u => xi u ∈ sup n S a)) ∧
            ∀ f, (V a f = true ↔ Pr xi yi (s.filter (fun u => xi u ∈ sup n S a)) M f) := by
        intro a ha b hb haw ma mb hsup disj hv tog
        apply ih a haw ha ma
        · intro i
          constructor
          · intro hi
            obtain ⟨u, hu, e⟩ := (hs i).1 ((hsup i).2 (Or.inl hi))
            refine ⟨u, Finset.mem_filter.2 ⟨hu, ?_⟩, e⟩
            rcases tog u hu with c | c
            · exact c.1
            · rcases e with e | e
              · exact (disj _ (e ▸ hi) c.1).elim
              · exact (disj _ (e ▸ hi) c.2).elim
          · rintro ⟨u, hu, e⟩
            rw [Finset.mem_filter] at hu
            rcases tog u hu.1 with c | c
            · rcases e with rfl | rfl
              · exact c.1
              · exact c.2
            · exact (disj _ hu.2 c.1).elim
        · intro u hu v hv'
          rw [Finset.mem_filter] at hu hv'
          have t := hval u hu.1 v hv'.1
          rw [hv] at t
          have ub : xi u ∉ sup n S b := fun c => disj _ hu.2 c
          have vb : yi v ∉ sup n S b := by
            intro c
            rcases tog v hv'.1 with d | d
            · exact disj _ d.2 c
            · exact disj _ hv'.2 d.1
          rw [offt b hb mb _ _ ub vb, Bool.or_false] at t
          exact t
        · intro z
          have := hsing z
          rw [hv] at this
          exact (Bool.or_eq_false_iff.1 this).1
      obtain ⟨Ma, hMa, sMa, va⟩ := part a ha b hb haw ma mb hsup disj hv tog
      obtain ⟨Mb, hMb, sMb, vb⟩ := part b hb a ha hbw mb ma (fun i => (hsup i).trans or_comm)
        (fun i x y => disj i y x) (fun f => by rw [hv, Bool.or_comm]) (fun u hu => (tog u hu).symm)
      have hsplit : s.filter (fun u => xi u ∈ sup n S a) ∪ s.filter (fun u => xi u ∈ sup n S b) = s := by
        rw [← Finset.filter_or]
        apply Finset.filter_true_of_mem
        intro u hu
        exact (inab u hu).1
      have hdj : Disjoint (s.filter (fun u => xi u ∈ sup n S a)) (s.filter (fun u => xi u ∈ sup n S b)) := by
        rw [Finset.disjoint_left]
        intro u h1 h2
        exact disj _ (Finset.mem_filter.1 h1).2 (Finset.mem_filter.1 h2).2
      obtain ⟨hM, hMs⟩ := isM_union _ _ Ma Mb hMa hMb sMa sMb hdj
      rw [hsplit] at hMs
      refine ⟨Ma ∪ Mb, hM, hMs, ?_⟩
      intro f
      rw [hv, Bool.or_eq_true, va, vb, ← Pr_union, hsplit]

theorem cls_z (z : ℕ) (hzx : ∀ u, z ≠ xi u) (hzy : ∀ u, z ≠ yi u) : ∀ w ∈ T, (∀ v ∈ S w, ¬ N v) →
    ∀ s : Finset (Fin k),
    (∀ i, i ∈ sup n S w ↔ i = z ∨ ∃ u ∈ s, i = xi u ∨ i = yi u) →
    (∀ u ∈ s, ∀ v ∈ s, V w (two (xi u) (yi v)) = decide (u = v)) →
    (∀ i, i ≠ z → V w (only i) = false) → V w (only z) = true →
    ∃ M : Finset (Finset (Fin k)), IsM M ∧ (∀ e ∈ M, e ⊆ s) ∧
      ∀ f, (V w f = true ↔ f z = true ∨ Pr xi yi s M f) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hm s hs hval hsing hz
    rcases H w hw with ⟨h1, h2, h3⟩ | ⟨h0, _, a, ha, b, hb, haw, hbw, hd, h, hv⟩ | ⟨_, hN, _⟩
    · have ez : z = w := by
        have := (hs z).2 (Or.inl rfl)
        rwa [sup_leaf h2 h1, Finset.mem_singleton] at this
      have es : s = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro u hu
        have := (hs (xi u)).2 (Or.inr ⟨u, hu, Or.inl rfl⟩)
        rw [sup_leaf h2 h1, Finset.mem_singleton] at this
        exact hzx u (ez.trans this.symm)
      refine ⟨∅, isM_empty, by simp, fun f => ?_⟩
      rw [h3, es, ez]
      simp [Pr]
    swap
    · exact absurd hN (hm w (self_mem H w hw))
    have ma : ∀ v ∈ S a, ¬ N v := fun v hv => hm v (by rw [h]; simp [hv])
    have mb : ∀ v ∈ S b, ¬ N v := fun v hv => hm v (by rw [h]; simp [hv])
    have hsup := sup_bin (n := n) h h0
    have disj : ∀ i, i ∈ sup n S a → i ∈ sup n S b → False := fun i => sup_disj hd
    have core : ∀ a ∈ T, ∀ b ∈ T, a < w → b < w → (∀ v ∈ S a, ¬ N v) → (∀ v ∈ S b, ¬ N v) →
        (∀ i, i ∈ sup n S w ↔ i ∈ sup n S a ∨ i ∈ sup n S b) →
        (∀ i, i ∈ sup n S a → i ∈ sup n S b → False) →
        (∀ f, V w f = (V a f || V b f)) → z ∈ sup n S a →
        ∃ M : Finset (Finset (Fin k)), IsM M ∧ (∀ e ∈ M, e ⊆ s) ∧
          ∀ f, (V w f = true ↔ f z = true ∨ Pr xi yi s M f) := by
      intro a ha b hb haw hbw ma mb hsup disj hv hza
      have zb : z ∉ sup n S b := disj z hza
      have bz : V b (only z) = false := by
        apply off H hb mb
        intro i hi
        have : i ≠ z := fun e => zb (e ▸ hi)
        simp [only, this]
      have asing : ∀ i, i ≠ z → V a (only i) = false := by
        intro i hi
        have := hsing i hi
        rw [hv] at this
        exact (Bool.or_eq_false_iff.1 this).1
      have bsing : ∀ i, V b (only i) = false := by
        intro i
        by_cases e : i = z
        · rw [e, bz]
        · have := hsing i e
          rw [hv] at this
          exact (Bool.or_eq_false_iff.1 this).2
      have az : V a (only z) = true := by
        have := hz
        rw [hv, bz, Bool.or_false] at this
        exact this
      have inab : ∀ u ∈ s, ∀ i, (i = xi u ∨ i = yi u) → i ∈ sup n S a ∨ i ∈ sup n S b :=
        fun u hu i e => (hsup i).1 ((hs i).2 (Or.inr ⟨u, hu, e⟩))
      have onel : ∀ c ∈ T, ∀ p q : ℕ, q ∉ sup n S c → V c (two p q) = V c (only p) := by
        intro c hc p q hq
        apply dep H c hc
        intro i hi
        have e : i ≠ q := fun e => hq (e ▸ hi)
        simp [two, only, e]
      have oner : ∀ c ∈ T, ∀ p q : ℕ, p ∉ sup n S c → V c (two p q) = V c (only q) := by
        intro c hc p q hp
        apply dep H c hc
        intro i hi
        have e : i ≠ p := fun e => hp (e ▸ hi)
        simp [two, only, e]
      have tog : ∀ u ∈ s, (xi u ∈ sup n S a ∧ yi u ∈ sup n S a) ∨ (xi u ∈ sup n S b ∧ yi u ∈ sup n S b) := by
        intro u hu
        have tr : V w (two (xi u) (yi u)) = true := by
          rw [hval u hu u hu]
          simp
        rw [hv] at tr
        rcases inab u hu _ (Or.inl rfl) with c1 | c1 <;> rcases inab u hu _ (Or.inr rfl) with c2 | c2
        · exact Or.inl ⟨c1, c2⟩
        · rw [onel a ha _ _ (fun c => disj _ c c2), oner b hb _ _ (fun c => disj _ c1 c),
            asing _ (hzx u).symm, bsing] at tr
          exact Bool.noConfusion tr
        · rw [oner a ha _ _ (fun c => disj _ c c1), onel b hb _ _ (fun c => disj _ c2 c),
            asing _ (hzy u).symm, bsing] at tr
          exact Bool.noConfusion tr
        · exact Or.inr ⟨c1, c2⟩
      let sa := s.filter (fun u => xi u ∈ sup n S a)
      let sb := s.filter (fun u => xi u ∈ sup n S b)
      have mema : ∀ u ∈ sa, xi u ∈ sup n S a ∧ yi u ∈ sup n S a := by
        intro u hu
        have hu' := Finset.mem_filter.1 hu
        rcases tog u hu'.1 with c | c
        · exact c
        · exact (disj _ hu'.2 c.1).elim
      have memb : ∀ u ∈ sb, xi u ∈ sup n S b ∧ yi u ∈ sup n S b := by
        intro u hu
        have hu' := Finset.mem_filter.1 hu
        rcases tog u hu'.1 with c | c
        · exact (disj _ c.1 hu'.2).elim
        · exact c
      have tos : ∀ u ∈ s, ∀ i, (i = xi u ∨ i = yi u) → (i ∈ sup n S a → u ∈ sa) ∧ (i ∈ sup n S b → u ∈ sb) := by
        intro u hu i e
        constructor
        · intro hi
          refine Finset.mem_filter.2 ⟨hu, ?_⟩
          rcases tog u hu with c | c
          · exact c.1
          · rcases e with e | e
            · exact (disj _ (e ▸ hi) c.1).elim
            · exact (disj _ (e ▸ hi) c.2).elim
        · intro hi
          refine Finset.mem_filter.2 ⟨hu, ?_⟩
          rcases tog u hu with c | c
          · rcases e with e | e
            · exact (disj _ c.1 (e ▸ hi)).elim
            · exact (disj _ c.2 (e ▸ hi)).elim
          · exact c.1
      obtain ⟨Ma, hMa, sMa, va⟩ := ih a haw ha ma sa (by
          intro i
          constructor
          · intro hi
            rcases (hs i).1 ((hsup i).2 (Or.inl hi)) with e | ⟨u, hu, e⟩
            · exact Or.inl e
            · exact Or.inr ⟨u, (tos u hu i e).1 hi, e⟩
          · rintro (rfl | ⟨u, hu, rfl | rfl⟩)
            · exact hza
            · exact (mema u hu).1
            · exact (mema u hu).2) (by
          intro u hu v hv'
          have t := hval u (Finset.mem_filter.1 hu).1 v (Finset.mem_filter.1 hv').1
          rw [hv] at t
          have : V b (two (xi u) (yi v)) = false := by
            apply off H hb mb
            intro i hi
            have e1 : i ≠ xi u := fun e => disj _ (mema u hu).1 (e ▸ hi)
            have e2 : i ≠ yi v := fun e => disj _ (mema v hv').2 (e ▸ hi)
            simp [two, e1, e2]
          rw [this, Bool.or_false] at t
          exact t) asing az
      obtain ⟨Mb, hMb, sMb, vb⟩ := cls_id H xi yi hx hy hxy b hb mb sb (by
          intro i
          constructor
          · intro hi
            rcases (hs i).1 ((hsup i).2 (Or.inr hi)) with e | ⟨u, hu, e⟩
            · exact (zb (e ▸ hi)).elim
            · exact ⟨u, (tos u hu i e).2 hi, e⟩
          · rintro ⟨u, hu, rfl | rfl⟩
            · exact (memb u hu).1
            · exact (memb u hu).2) (by
          intro u hu v hv'
          have t := hval u (Finset.mem_filter.1 hu).1 v (Finset.mem_filter.1 hv').1
          rw [hv] at t
          have : V a (two (xi u) (yi v)) = false := by
            have e1 : xi u ∉ sup n S a := fun c => disj _ c (memb u hu).1
            have e2 : yi v ∉ sup n S a := fun c => disj _ c (memb v hv').2
            have : V a (two (xi u) (yi v)) = V a zero := by
              apply dep H a ha
              intro i hi
              have f1 : i ≠ xi u := fun e => e1 (e ▸ hi)
              have f2 : i ≠ yi v := fun e => e2 (e ▸ hi)
              simp [two, zero, f1, f2]
            rw [this, mono_zero H a ha ma]
          rw [this, Bool.false_or] at t
          exact t) bsing
      have hsplit : sa ∪ sb = s := by
        simp only [sa, sb]
        rw [← Finset.filter_or]
        apply Finset.filter_true_of_mem
        intro u hu
        exact inab u hu _ (Or.inl rfl)
      have hdj : Disjoint sa sb := by
        rw [Finset.disjoint_left]
        intro u h1 h2
        exact disj _ (Finset.mem_filter.1 h1).2 (Finset.mem_filter.1 h2).2
      obtain ⟨hM, hMs⟩ := isM_union _ _ Ma Mb hMa hMb sMa sMb hdj
      rw [hsplit] at hMs
      refine ⟨Ma ∪ Mb, hM, hMs, ?_⟩
      intro f
      rw [hv, Bool.or_eq_true, va, vb, or_assoc, ← Pr_union, hsplit]
    rcases hv with hv | hv
    · exfalso
      rw [hv, Bool.and_eq_true] at hz
      have off1 : ∀ c ∈ T, (∀ v ∈ S c, ¬ N v) → z ∉ sup n S c → V c (only z) = false := by
        intro c hc mc hzc
        apply off H hc mc
        intro i hi
        have : i ≠ z := fun e => hzc (e ▸ hi)
        simp [only, this]
      by_cases c : z ∈ sup n S a
      · have := off1 b hb mb (disj z c)
        rw [hz.2] at this
        exact Bool.noConfusion this
      · have := off1 a ha ma c
        rw [hz.1] at this
        exact Bool.noConfusion this
    · rcases (hsup z).1 ((hs z).2 (Or.inl rfl)) with c | c
      · exact core a ha b hb haw hbw ma mb hsup disj hv c
      · exact core b hb a ha hbw haw mb ma (fun i => (hsup i).trans or_comm) (fun i x y => disj i y x)
          (fun f => by rw [hv, Bool.or_comm]) c

end classify

theorem no_crown {n : ℕ} {T : Finset ℕ} {V : ℕ → (ℕ → Bool) → Bool} {S : ℕ → Finset ℕ} {N : ℕ → Prop}
    (H : ∀ w ∈ T, Node n T V S N w) {k : ℕ} (hk : 3 ≤ k) (xi yi : Fin k → ℕ)
    (hx : ∀ u v, xi u = xi v → u = v) (hy : ∀ u v, yi u = yi v → u = v) (hxy : ∀ u v, xi u ≠ yi v)
    (z : ℕ) (hzx : ∀ u, z ≠ xi u) (hzy : ∀ u, z ≠ yi u) :
    ∀ w ∈ T, (∀ v ∈ S w, ¬ N v) →
      (∀ u v, V w (two (xi u) (yi v)) = decide (u ≠ v)) →
      (∀ u, V w (two (xi u) z) = true) → V w (only z) = false → False := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hm hval hcol hz
    have p0 : 0 < k := by omega
    have p1 : 1 < k := by omega
    have p2 : 2 < k := by omega
    let i0 : Fin k := ⟨0, p0⟩
    let i1 : Fin k := ⟨1, p1⟩
    let i2 : Fin k := ⟨2, p2⟩
    have n01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
    have n02 : i0 ≠ i2 := by simp [i0, i2, Fin.ext_iff]
    have n12 : i1 ≠ i2 := by simp [i1, i2, Fin.ext_iff]
    have sing : ∀ u, V w (only (xi u)) = false ∧ V w (only (yi u)) = false := by
      intro u
      have h0 : V w (two (xi u) (yi u)) = false := by
        rw [hval]
        simp
      constructor
      · by_contra c
        rw [Bool.not_eq_false] at c
        have := mono H w hw hm (only (xi u)) (two (xi u) (yi u)) (fun i hi => by
          simp only [only, two, decide_eq_true_eq] at hi ⊢
          exact Or.inl hi) c
        rw [h0] at this
        exact Bool.noConfusion this
      · by_contra c
        rw [Bool.not_eq_false] at c
        have := mono H w hw hm (only (yi u)) (two (xi u) (yi u)) (fun i hi => by
          simp only [only, two, decide_eq_true_eq] at hi ⊢
          exact Or.inr hi) c
        rw [h0] at this
        exact Bool.noConfusion this
    rcases H w hw with ⟨_, _, h3⟩ | ⟨h0, _, a, ha, b, hb, haw, hbw, hd, h, hv⟩ | ⟨_, hN, _⟩
    · have e1 := hval i0 i1
      have e2 := hval i1 i0
      rw [h3] at e1 e2
      simp only [two, n01, n01.symm, ne_eq, not_false_eq_true, decide_true, decide_eq_true_eq] at e1 e2
      rcases e1 with e1 | e1 <;> rcases e2 with e2 | e2
      · exact n01 (hx _ _ (e1.symm.trans e2))
      · exact hxy _ _ (e1.symm.trans e2)
      · exact hxy _ _ (e2.symm.trans e1)
      · exact n01 (hy _ _ (e2.symm.trans e1))
    swap
    · exact absurd hN (hm w (self_mem H w hw))
    have ma : ∀ v ∈ S a, ¬ N v := fun v hv => hm v (by rw [h]; simp [hv])
    have mb : ∀ v ∈ S b, ¬ N v := fun v hv => hm v (by rw [h]; simp [hv])
    have hsup := sup_bin (n := n) h h0
    have disj : ∀ i, i ∈ sup n S a → i ∈ sup n S b → False := fun i => sup_disj hd
    have onel : ∀ c ∈ T, ∀ p q : ℕ, q ∉ sup n S c → V c (two p q) = V c (only p) := by
      intro c hc p q hq
      apply dep H c hc
      intro i hi
      have e : i ≠ q := fun e => hq (e ▸ hi)
      simp [two, only, e]
    have oner : ∀ c ∈ T, ∀ p q : ℕ, p ∉ sup n S c → V c (two p q) = V c (only q) := by
      intro c hc p q hp
      apply dep H c hc
      intro i hi
      have e : i ≠ p := fun e => hp (e ▸ hi)
      simp [two, only, e]
    rcases hv with hv | hv
    · have nab : V a zero = false ∧ V b zero = false := ⟨mono_zero H a ha ma, mono_zero H b hb mb⟩
      have both : ∀ u v : Fin k, u ≠ v → V a (two (xi u) (yi v)) = true ∧ V b (two (xi u) (yi v)) = true := by
        intro u v huv
        have := hval u v
        rw [hv] at this
        simpa [huv] using this
      have one : ∀ c ∈ T, (∀ v ∈ S c, ¬ N v) → ∀ p q : ℕ, V c (two p q) = true →
          p ∈ sup n S c ∨ q ∈ sup n S c := by
        intro c hc mc p q ht
        by_contra c'
        rw [not_or] at c'
        have : V c (two p q) = false := by
          apply off H hc mc
          intro i hi
          have e1 : i ≠ p := fun e => c'.1 (e ▸ hi)
          have e2 : i ≠ q := fun e => c'.2 (e ▸ hi)
          simp [two, e1, e2]
        rw [this] at ht
        exact Bool.noConfusion ht
      have core : ∀ a ∈ T, ∀ b ∈ T, (∀ v ∈ S a, ¬ N v) → (∀ v ∈ S b, ¬ N v) →
          (∀ i, i ∈ sup n S a → i ∈ sup n S b → False) →
          (∀ u v : Fin k, u ≠ v → V a (two (xi u) (yi v)) = true ∧ V b (two (xi u) (yi v)) = true) →
          (∀ f, V w f = (V a f && V b f)) → xi i0 ∈ sup n S a → False := by
        intro a ha b hb ma mb disj both hv h0a
        have split : ∀ u v : Fin k, u ≠ v →
            (xi u ∈ sup n S a → yi v ∈ sup n S b) ∧ (yi v ∈ sup n S b → xi u ∈ sup n S a) := by
          intro u v huv
          have c1 := one a ha ma _ _ (both u v huv).1
          have c2 := one b hb mb _ _ (both u v huv).2
          constructor
          · intro h1
            rcases c2 with c2 | c2
            · exact (disj _ h1 c2).elim
            · exact c2
          · intro h2
            rcases c1 with c1 | c1
            · exact c1
            · exact (disj _ c1 h2).elim
        have y1 := (split i0 i1 n01).1 h0a
        have x2 := (split i2 i1 n12.symm).2 y1
        have y0 := (split i2 i0 n02.symm).1 x2
        have y2 := (split i0 i2 n02).1 h0a
        have x1 := (split i1 i2 n12).2 y2
        have e1 : V a (two (xi i0) (yi i0)) = true := by
          rw [onel a ha _ _ (fun c => disj _ c y0), ← onel a ha _ (yi i1) (fun c => disj _ c y1)]
          exact (both i0 i1 n01).1
        have e2 : V b (two (xi i0) (yi i0)) = true := by
          rw [oner b hb _ _ (fun c => disj _ h0a c), ← oner b hb (xi i1) _ (fun c => disj _ x1 c)]
          exact (both i1 i0 n01.symm).2
        have := hval i0 i0
        rw [hv, e1, e2] at this
        simp at this
      rcases one a ha ma _ _ (both i0 i1 n01).1 with c | c
      · exact core a ha b hb ma mb disj both hv c
      · have xb : xi i0 ∈ sup n S b := by
          rcases one b hb mb _ _ (both i0 i1 n01).2 with d | d
          · exact d
          · exact (disj _ c d).elim
        exact core b hb a ha mb ma (fun i x y => disj i y x) (fun u v huv => (both u v huv).symm)
          (fun f => by rw [hv, Bool.and_comm]) xb
    · have sa : ∀ i, V w (only i) = false → V a (only i) = false ∧ V b (only i) = false := by
        intro i hi
        rw [hv] at hi
        exact Bool.or_eq_false_iff.1 hi
      have same : ∀ c ∈ T, ∀ u v : Fin k, V c (two (xi u) (yi v)) = true → V c (only (xi u)) = false →
          V c (only (yi v)) = false → xi u ∈ sup n S c ∧ yi v ∈ sup n S c := by
        intro c hc u v ht h1 h2
        constructor
        · by_contra d
          rw [oner c hc _ _ d, h2] at ht
          exact Bool.noConfusion ht
        · by_contra d
          rw [onel c hc _ _ d, h1] at ht
          exact Bool.noConfusion ht
      have core : ∀ a ∈ T, ∀ b ∈ T, a < w → (∀ v ∈ S a, ¬ N v) → (∀ v ∈ S b, ¬ N v) →
          (∀ i, i ∈ sup n S a → i ∈ sup n S b → False) →
          (∀ f, V w f = (V a f || V b f)) → xi i0 ∈ sup n S a → False := by
        intro a ha b hb haw ma mb disj hv h0a
        have sa : ∀ i, V w (only i) = false → V a (only i) = false ∧ V b (only i) = false := by
          intro i hi
          rw [hv] at hi
          exact Bool.or_eq_false_iff.1 hi
        have link : ∀ u v : Fin k, u ≠ v → (xi u ∈ sup n S a ↔ yi v ∈ sup n S a) := by
          intro u v huv
          have t := hval u v
          rw [hv] at t
          simp only [huv, ne_eq, not_false_eq_true, decide_true, Bool.or_eq_true] at t
          rcases t with t | t
          · have := same a ha u v t (sa _ (sing u).1).1 (sa _ (sing v).2).1
            exact ⟨fun _ => this.2, fun _ => this.1⟩
          · have := same b hb u v t (sa _ (sing u).1).2 (sa _ (sing v).2).2
            exact ⟨fun c => (disj _ c this.1).elim, fun c => (disj _ c this.2).elim⟩
        have y1 := (link i0 i1 n01).1 h0a
        have x2 := (link i2 i1 n12.symm).2 y1
        have y0 := (link i2 i0 n02.symm).1 x2
        have y2 := (link i0 i2 n02).1 h0a
        have x1 := (link i1 i2 n12).2 y2
        have ally : ∀ v : Fin k, yi v ∈ sup n S a := by
          intro v
          by_cases c : v = i0
          · exact c ▸ y0
          · exact (link i0 v (Ne.symm c)).1 h0a
        have allx : ∀ u : Fin k, xi u ∈ sup n S a := by
          intro u
          by_cases c : u = i1
          · exact c ▸ x1
          · exact (link u i1 c).2 y1
        have xnb : ∀ u, xi u ∉ sup n S b := fun u c => disj _ (allx u) c
        have ynb : ∀ u, yi u ∉ sup n S b := fun u c => disj _ (ally u) c
        have znb : z ∉ sup n S b := by
          intro zb
          have t := hcol i0
          rw [hv, oner b hb _ _ (xnb i0), (sa z hz).2, Bool.or_false,
            onel a ha _ _ (fun c => disj _ c zb), (sa _ (sing i0).1).1] at t
          exact Bool.noConfusion t
        have bz : ∀ p q : ℕ, (p = z ∨ p ∉ sup n S b) → (q = z ∨ q ∉ sup n S b) → V b (two p q) = false := by
          intro p q hp hq
          apply off H hb mb
          intro i hi
          have e1 : i ≠ p := by
            intro e
            rcases hp with d | d
            · exact znb (d ▸ e ▸ hi)
            · exact d (e ▸ hi)
          have e2 : i ≠ q := by
            intro e
            rcases hq with d | d
            · exact znb (d ▸ e ▸ hi)
            · exact d (e ▸ hi)
          simp [two, e1, e2]
        apply ih a haw ha ma
        · intro u v
          have t := hval u v
          rw [hv, bz _ _ (Or.inr (xnb u)) (Or.inr (ynb v)), Bool.or_false] at t
          exact t
        · intro u
          have t := hcol u
          rw [hv, bz _ _ (Or.inr (xnb u)) (Or.inl rfl), Bool.or_false] at t
          exact t
        · exact (sa z hz).1
      have t := hval i0 i1
      rw [hv] at t
      simp only [n01, ne_eq, not_false_eq_true, decide_true, Bool.or_eq_true] at t
      rcases t with t | t
      · exact core a ha b hb haw ma mb disj hv
          (same a ha _ _ t (sa _ (sing i0).1).1 (sa _ (sing i1).2).1).1
      · exact core b hb a ha hbw mb ma (fun i x y => disj i y x) (fun f => by rw [hv, Bool.or_comm])
          (same b hb _ _ t (sa _ (sing i0).1).2 (sa _ (sing i1).2).2).1

section circ

variable (C : Circuit) (n : ℕ)

def val (o : ℕ) (f : ℕ → Bool) : Bool := value C (inp n f) o

theorem inp_len (f : ℕ → Bool) : (inp n f).length = n := by simp [inp]

theorem val_input (o : ℕ) (ho : o < n) (f : ℕ → Bool) : val C n o f = f o := by
  change (run C.gates (inp n f)).getD o false = f o
  rw [prefix_keep _ _ (by rw [inp_len]; exact ho)]
  simp [inp, List.getD_eq_getElem?_getD, ho]

theorem val_gate (o : ℕ) (ho : n ≤ o) (hj : o - n < C.gates.length) (f : ℕ → Bool) :
    val C n o f = (gateAt C n o).op.eval
      ((gateAt C n o).inputs.map fun i => if i < o then val C n i f else false) := by
  have hnw : n + (o - n) = o := by omega
  have := value_gate C (inp n f) (o - n) (by exact hj)
  rw [inp_len, hnw] at this
  rw [gateAt_eq C n hj]
  exact this

theorem val_out (o : ℕ) (ho : n + C.gates.length ≤ o) (f : ℕ → Bool) : val C n o f = false := by
  change (run C.gates (inp n f)).getD o false = false
  have : (run C.gates (inp n f)).length ≤ o := by
    rw [run_length, inp_len]
    exact ho
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none_iff.2 this]

theorem mem_ch {w i : ℕ} (hn : n ≤ w) (hj : w - n < C.gates.length) (hi : i ∈ reads C n w) (hiw : i < w) :
    i ∈ ch C n w := by
  unfold ch
  rw [if_pos ⟨hn, hj⟩, List.mem_filter]
  exact ⟨hi, by simpa using hiw⟩

theorem dep0 : ∀ w, ∀ f g : ℕ → Bool, (∀ i ∈ desc C n w, i < n → f i = g i) → val C n w f = val C n w g := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro f g h
    by_cases h1 : w < n
    · rw [val_input C n w h1, val_input C n w h1]
      exact h w (self_desc C n w) h1
    by_cases h2 : n + C.gates.length ≤ w
    · rw [val_out C n w h2, val_out C n w h2]
    have hn : n ≤ w := by omega
    have hj : w - n < C.gates.length := by omega
    rw [val_gate C n w hn hj, val_gate C n w hn hj]
    have key : ∀ i ∈ reads C n w, (if i < w then val C n i f else false) =
        (if i < w then val C n i g else false) := by
      intro i hi
      split
      · rename_i hiw
        have hc := mem_ch C n hn hj hi hiw
        apply ih i hiw
        intro v hv
        exact h v ((mem_desc C n w v).2 (Or.inr ⟨i, hc, hv⟩))
      · rfl
    unfold reads at key
    by_cases hop : (gateAt C n w).op = GateOp.not
    · rw [if_pos hop] at key
      rw [hop]
      cases hin : (gateAt C n w).inputs with
      | nil => rfl
      | cons a l =>
        rw [hin] at key
        have := key a (by simp)
        simp only [GateOp.eval, List.map_cons, List.headD_cons, this]
    · rw [if_neg hop] at key
      congr 1
      exact List.map_congr_left key

theorem mono0 (hg : GoodC C) : ∀ w, (∀ v ∈ desc C n w, ¬ isNot C n v) → ∀ f g : ℕ → Bool,
    (∀ i, f i = true → g i = true) → val C n w f = true → val C n w g = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hm f g hfg
    by_cases h1 : w < n
    · rw [val_input C n w h1, val_input C n w h1]
      exact hfg w
    by_cases h2 : n + C.gates.length ≤ w
    · rw [val_out C n w h2]
      exact fun h => (Bool.noConfusion h)
    have hn : n ≤ w := by omega
    have hj : w - n < C.gates.length := by omega
    rw [val_gate C n w hn hj, val_gate C n w hn hj]
    have hop : (gateAt C n w).op ≠ GateOp.not := fun c => hm w (self_desc C n w) ⟨hn, c⟩
    have hg' : (gateAt C n w).op = GateOp.and ∨ (gateAt C n w).op = GateOp.or := by
      rw [gateAt_eq C n hj] at hop ⊢
      rcases (hg _ (List.getElem_mem hj)).1 with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd h hop
    have key : ∀ i ∈ (gateAt C n w).inputs, (if i < w then val C n i f else false) = true →
        (if i < w then val C n i g else false) = true := by
      intro i hi
      split
      · rename_i hiw
        have hc : i ∈ ch C n w := mem_ch C n hn hj (by unfold reads; rw [if_neg hop]; exact hi) hiw
        apply ih i hiw _ f g hfg
        intro v hv
        exact hm v ((mem_desc C n w v).2 (Or.inr ⟨i, hc, hv⟩))
      · exact id
    rcases hg' with h | h <;> rw [h] <;>
      simp only [GateOp.eval, List.all_eq_true, List.any_eq_true, List.mem_map, id]
    · rintro p b ⟨i, hi, rfl⟩
      exact key i hi (p _ ⟨i, hi, rfl⟩)
    · rintro ⟨b, ⟨i, hi, rfl⟩, p⟩
      exact ⟨_, ⟨i, hi, rfl⟩, key i hi p⟩

theorem gates_le (o : ℕ) (ho : o < n + C.gates.length) : (gatesIn C n o).card ≤ C.gates.length := by
  have : gatesIn C n o ⊆ Finset.Ico n (n + C.gates.length) := by
    intro v hv
    have hv' := Finset.mem_filter.1 hv
    have := desc_le C n o v hv'.1
    rw [Finset.mem_Ico]
    exact ⟨hv'.2, by omega⟩
  have := Finset.card_le_card this
  rw [Nat.card_Ico] at this
  omega

theorem sup_eq_leaves (o : ℕ) : sup n (desc C n) o = leaves C n o := rfl

end circ

theorem class_id (k : ℕ) (hk : 2 ≤ k) (C : Circuit) (hg : GoodC C)
    (hmon : ∀ g ∈ C.gates, g.op ≠ GateOp.not) (hsize : C.gates.length + 1 ≤ 2 * k)
    (hrep : ∀ u v : Fin k, val C (k + k) C.output (two u.val (k + v.val)) = decide (u = v)) :
    ∃ M : Finset (Finset (Fin k)), IsM M ∧ ∀ f,
      (val C (k + k) C.output f = true ↔ Pr (fun u => u.val) (fun u => k + u.val) Finset.univ M f) := by
  have hnot : ∀ v, ¬ isNot C (k + k) v := by
    intro v h
    have h2 := h.2
    unfold gateAt at h2
    by_cases c : v - (k + k) < C.gates.length
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem c] at h2
      exact hmon _ (List.getElem_mem c) h2
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none_iff.2 (by omega)] at h2
      exact GateOp.noConfusion h2
  have ho : C.output < k + k + C.gates.length := by
    by_contra c
    have := hrep ⟨0, by omega⟩ ⟨0, by omega⟩
    rw [val_out C _ _ (by omega)] at this
    simp at this
  have other : ∀ u : Fin k, ∃ w : Fin k, w ≠ u := by
    intro u
    by_cases c : u.val = 0
    · exact ⟨⟨1, by omega⟩, by simp [Fin.ext_iff, c]⟩
    · exact ⟨⟨0, by omega⟩, by simp [Fin.ext_iff, eq_comm, c]⟩
  have mo := mono0 C (k + k) hg C.output (fun v _ => hnot v)
  have fx : ∀ u : Fin k, val C (k + k) C.output (only u.val) = false ∧
      val C (k + k) C.output (only (k + u.val)) = false := by
    intro u
    obtain ⟨w, hw⟩ := other u
    constructor
    · by_contra c
      rw [Bool.not_eq_false] at c
      have := mo (only u.val) (two u.val (k + w.val)) (fun i hi => by
        simp only [only, two, decide_eq_true_eq] at hi ⊢
        exact Or.inl hi) c
      rw [hrep] at this
      simp [Ne.symm hw] at this
    · by_contra c
      rw [Bool.not_eq_false] at c
      have := mo (only (k + u.val)) (two w.val (k + u.val)) (fun i hi => by
        simp only [only, two, decide_eq_true_eq] at hi ⊢
        exact Or.inr hi) c
      rw [hrep] at this
      simp [hw] at this
  have hleaf : ∀ i < k + k, i ∈ desc C (k + k) C.output := by
    intro i hi
    by_contra c
    have key : ∀ u : Fin k, (i = u.val ∨ i = k + u.val) → False := by
      intro u e
      have h1 := hrep u u
      simp only [decide_true] at h1
      rcases e with e | e
      · have : val C (k + k) C.output (two u.val (k + u.val)) =
            val C (k + k) C.output (only (k + u.val)) := by
          apply dep0
          intro v hv _
          have : v ≠ u.val := fun d => c (e ▸ d ▸ hv)
          simp [two, only, this]
        rw [this, (fx u).2] at h1
        exact Bool.noConfusion h1
      · have : val C (k + k) C.output (two u.val (k + u.val)) = val C (k + k) C.output (only u.val) := by
          apply dep0
          intro v hv _
          have : v ≠ k + u.val := fun d => c (e ▸ d ▸ hv)
          simp [two, only, this]
        rw [this, (fx u).1] at h1
        exact Bool.noConfusion h1
    by_cases d : i < k
    · exact key ⟨i, d⟩ (Or.inl rfl)
    · exact key ⟨i - k, by omega⟩ (Or.inr (show i = k + (i - k) by omega))
  have hL : leaves C (k + k) C.output = Finset.range (k + k) := by
    ext i
    unfold leaves
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨fun h => h.2, fun h => ⟨hleaf i h, h⟩⟩
  have hex : (gatesIn C (k + k) C.output).card + 1 ≤
      (leaves C (k + k) C.output).card + (nots C (k + k) C.output).card := by
    have := gates_le C (k + k) C.output ho
    rw [hL, Finset.card_range]
    omega
  have H := tree_nodes C (k + k) hg C.output ho hex
  have hs : sup (k + k) (desc C (k + k)) C.output = Finset.range (k + k) := hL
  have hself := self_desc C (k + k) C.output
  obtain ⟨M, hM, _, hv⟩ := cls_id H (fun u : Fin k => u.val) (fun u : Fin k => k + u.val)
    (fun u v h => Fin.ext h) (fun u v h => Fin.ext (by omega)) (fun u v h => by have := u.isLt; omega)
    C.output hself (fun v _ => hnot v) Finset.univ (by
      intro i
      rw [hs, Finset.mem_range]
      constructor
      · intro hi
        by_cases d : i < k
        · exact ⟨⟨i, d⟩, Finset.mem_univ _, Or.inl rfl⟩
        · exact ⟨⟨i - k, by omega⟩, Finset.mem_univ _, Or.inr (show i = k + (i - k) by omega)⟩
      · rintro ⟨u, _, rfl | rfl⟩ <;> have := u.isLt <;> omega)
    (fun u _ v _ => hrep u v)
    (by
      intro z
      change val C (k + k) C.output (only z) = false
      by_cases d : z < k
      · exact (fx ⟨z, d⟩).1
      by_cases e : z < k + k
      · have := (fx ⟨z - k, by omega⟩).2
        have ez : k + (z - k) = z := by omega
        simpa [ez] using this
      refine off H hself (fun v _ => hnot v) _ ?_
      intro i hi
      rw [hs, Finset.mem_range] at hi
      have : i ≠ z := by omega
      simp [only, this])
  exact ⟨M, hM, hv⟩

def Qc (k u v : ℕ) : Prop := u ≠ k + 1 ∧ ¬ (u < k ∧ u = v)

theorem rows_distinct (k : ℕ) (hk : 2 ≤ k) (u u' : ℕ) (hu : u < k + 2) (hu' : u' < k + 2)
    (h : ∀ v < k + 1, (Qc k u v ↔ Qc k u' v)) : u = u' := by
  unfold Qc at h
  by_contra c
  have hk0 := h k (by omega)
  by_cases a : u < k
  · have h1 := h u (by omega)
    omega
  by_cases b : u' < k
  · have h1 := h u' (by omega)
    omega
  omega

theorem cols_distinct (k : ℕ) (v v' : ℕ) (hv : v < k + 1) (hv' : v' < k + 1)
    (h : ∀ u < k + 2, (Qc k u v ↔ Qc k u v')) : v = v' := by
  unfold Qc at h
  by_contra c
  by_cases a : v < k
  · have h1 := h v (by omega)
    omega
  · have h1 := h v' (by omega)
    omega

theorem avoid (k : ℕ) (hk : 5 ≤ k) (a b c d : ℕ) : ∃ u, u < k ∧ u ≠ a ∧ u ≠ b ∧ u ≠ c ∧ u ≠ d := by
  have : ¬ Finset.range 5 ⊆ {a, b, c, d} := by
    intro h
    have h1 := Finset.card_le_card h
    have h2 : ({a, b, c, d} : Finset ℕ).card ≤ 4 := Finset.card_le_four
    rw [Finset.card_range] at h1
    omega
  rw [Finset.not_subset] at this
  obtain ⟨u, hu, hn⟩ := this
  rw [Finset.mem_range] at hu
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
  exact ⟨u, by omega, hn.1, hn.2.1, hn.2.2.1, hn.2.2.2⟩

theorem almost_all (m : ℕ) (p : ℕ → Prop) [DecidablePred p]
    (h : ∀ a b, a < m → b < m → ¬ p a → ¬ p b → a = b) : m ≤ ((Finset.range m).filter p).card + 1 := by
  have h1 : ((Finset.range m).filter (fun a => ¬ p a)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    rw [Finset.mem_filter, Finset.mem_range] at ha hb
    exact h a b ha.1 hb.1 ha.2 hb.2
  have h2 := Finset.card_filter_add_card_filter_not (s := Finset.range m) p
  rw [Finset.card_range] at h2
  omega

section single

variable (C : Circuit) (n o ν c : ℕ)
  (H : ∀ w ∈ desc C n o, Node n (desc C n o) (fun w f => value C (inp n f) w) (desc C n) (isNot C n) w)
  (huni : ∀ v ∈ desc C n o, isNot C n v → v = ν)
  (hν : isNot C n ν) (hc : c < ν) (hcT : c ∈ desc C n o)
  (hS : desc C n ν = insert ν (desc C n c))
  (hV : ∀ f, val C n ν f = !val C n c f)

include huni hc

theorem below_c : ∀ v ∈ desc C n c, v ∈ desc C n o → ¬ isNot C n v := by
  intro v hv hvo h
  have := huni v hvo h
  have := desc_le C n c v hv
  omega

theorem nonu {w : ℕ} (hw : w ∈ desc C n o) (h : ν ∉ desc C n w) : ∀ v ∈ desc C n w, ¬ isNot C n v := by
  intro v hv hn
  have := huni v (desc_trans C n o w hw hv) hn
  exact h (this ▸ hv)

include H hcT hS

theorem sup_c_sub {a : ℕ} (h : ν ∈ desc C n a) : ∀ i ∈ sup n (desc C n) c, i ∈ sup n (desc C n) a := by
  intro i hi
  have hi' := Finset.mem_filter.1 hi
  refine Finset.mem_filter.2 ⟨desc_trans C n a ν h ?_, hi'.2⟩
  rw [hS]
  exact Finset.mem_insert_of_mem hi'.1

theorem step_nu : ∀ w ∈ desc C n o, ν ∈ desc C n w → w ≠ ν →
    ∃ a ∈ desc C n o, ∃ b ∈ desc C n o, a < w ∧ ν ∈ desc C n a ∧ ν ∉ desc C n b ∧
      (∀ i ∈ sup n (desc C n) b, i ∉ sup n (desc C n) c) ∧
      (∀ i, i ∈ sup n (desc C n) w ↔ i ∈ sup n (desc C n) a ∨ i ∈ sup n (desc C n) b) ∧
      ((∀ f, val C n w f = (val C n a f && val C n b f)) ∨ ∀ f, val C n w f = (val C n a f || val C n b f)) := by
  intro w hw hνw hne
  have hlev := desc_le C n w ν hνw
  rcases H w hw with ⟨h1, h2, _⟩ | ⟨h0, _, a, ha, b, hb, haw, _, hd, h, hv⟩ | ⟨_, hN, _⟩
  · rw [h2, Finset.mem_singleton] at hνw
    exact absurd hνw.symm hne
  · have key : ∀ a ∈ desc C n o, ∀ b ∈ desc C n o, a < w → Disjoint (desc C n a) (desc C n b) →
        desc C n w = insert w (desc C n a ∪ desc C n b) → ν ∈ desc C n a →
        ((∀ f, val C n w f = (val C n a f && val C n b f)) ∨ ∀ f, val C n w f = (val C n a f || val C n b f)) →
        ∃ a ∈ desc C n o, ∃ b ∈ desc C n o, a < w ∧ ν ∈ desc C n a ∧ ν ∉ desc C n b ∧
          (∀ i ∈ sup n (desc C n) b, i ∉ sup n (desc C n) c) ∧
          (∀ i, i ∈ sup n (desc C n) w ↔ i ∈ sup n (desc C n) a ∨ i ∈ sup n (desc C n) b) ∧
          ((∀ f, val C n w f = (val C n a f && val C n b f)) ∨
            ∀ f, val C n w f = (val C n a f || val C n b f)) := by
      intro a ha b hb haw hd h hνa hv
      refine ⟨a, ha, b, hb, haw, hνa, Finset.disjoint_left.1 hd hνa, ?_, sup_bin h h0, hv⟩
      intro i hib hic
      exact sup_disj hd (sup_c_sub C n o ν c H huni hc hcT hS hνa i hic) hib
    rw [h, Finset.mem_insert, Finset.mem_union] at hνw
    rcases hνw with e | e | e
    · exact absurd e.symm hne
    · exact key a ha b hb haw hd h e hv
    · refine key b hb a ha (by assumption) hd.symm (by rw [h, Finset.union_comm]) e ?_
      rcases hv with hv | hv
      · exact Or.inl fun f => (hv f).trans (Bool.and_comm _ _)
      · exact Or.inr fun f => (hv f).trans (Bool.or_comm _ _)
  · have := huni w hw hN
    exact absurd this hne

include hV

theorem polar : ∀ w ∈ desc C n o, ν ∈ desc C n w → ∀ f g : ℕ → Bool,
    (∀ i, i ∉ sup n (desc C n) c → f i = true → g i = true) →
    (∀ i ∈ sup n (desc C n) c, g i = true → f i = true) →
    val C n w f = true → val C n w g = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hνw f g h1 h2
    by_cases e : w = ν
    · subst e
      rw [hV, hV]
      have mc : val C n c g = true → val C n c f = true := by
        intro hg
        let g' : ℕ → Bool := fun i => if i ∈ sup n (desc C n) c then g i else false
        have e1 : val C n c g = val C n c g' := by
          apply dep H c hcT
          intro i hi
          simp only [g', if_pos hi]
        apply mono H c hcT (fun v hv => below_c C n o _ c huni hc v hv (desc_trans C n o c hcT hv)) g' f _
          (e1.symm.trans hg)
        intro i hi
        simp only [g'] at hi
        split at hi
        · rename_i d
          exact h2 i d hi
        · exact Bool.noConfusion hi
      intro h
      cases hg : val C n c g
      · rfl
      · rw [mc hg] at h
        exact Bool.noConfusion h
    · obtain ⟨a, ha, b, hb, haw, hνa, hνb, hbc, _, hv⟩ :=
        step_nu C n o ν c H huni hc hcT hS w hw hνw e
      have ia := ih a haw ha hνa f g h1 h2
      have ib : val C n b f = true → val C n b g = true := by
        intro hf
        let f' : ℕ → Bool := fun i => if i ∈ sup n (desc C n) b then f i else false
        have e1 : val C n b f = val C n b f' := by
          apply dep H b hb
          intro i hi
          simp only [f', if_pos hi]
        apply mono H b hb (nonu C n o ν c huni hc hb hνb) f' g _ (e1.symm.trans hf)
        intro i hi
        simp only [f'] at hi
        split at hi
        · rename_i d
          exact h1 i (hbc i d) hi
        · exact Bool.noConfusion hi
      rcases hv with hv | hv <;> rw [hv, hv]
      · simp only [Bool.and_eq_true]
        exact fun p => ⟨ia p.1, ib p.2⟩
      · simp only [Bool.or_eq_true]
        exact fun p => p.imp ia ib

theorem bit : ∀ w ∈ desc C n o, ν ∈ desc C n w → ∀ f g : ℕ → Bool,
    (∀ i, i ∉ sup n (desc C n) c → f i = g i) → val C n c f = val C n c g →
    val C n w f = val C n w g := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hνw f g h1 h2
    by_cases e : w = ν
    · subst e
      rw [hV, hV, h2]
    · obtain ⟨a, ha, b, hb, haw, hνa, _, hbc, _, hv⟩ :=
        step_nu C n o ν c H huni hc hcT hS w hw hνw e
      have ia := ih a haw ha hνa f g h1 h2
      have ib : val C n b f = val C n b g := dep H b hb f g (fun i hi => h1 i (hbc i hi))
      rcases hv with hv | hv <;> rw [hv, hv, ia, ib]

omit hV in
theorem outside (hνo : ν ∈ desc C n o) (hne : o ≠ ν) :
    ∃ i ∈ sup n (desc C n) o, i ∉ sup n (desc C n) c := by
  obtain ⟨a, _, b, hb, _, _, _, hbc, hsup, _⟩ :=
    step_nu C n o ν c H huni hc hcT hS o (self_desc C n o) hνo hne
  obtain ⟨i, hi⟩ := sup_ne H b hb
  exact ⟨i, (hsup i).2 (Or.inr hi), hbc i hi⟩

end single

theorem class_crown (k : ℕ) (hk : 7 ≤ k) (C : Circuit) (hg : GoodC C) (hsize : C.gates.length ≤ 2 * k + 1)
    (hrep : ∀ u < k + 2, ∀ v < k + 1,
      (val C (k + 2 + (k + 1)) C.output (two u (k + 2 + v)) = true ↔ Qc k u v)) :
    ∃ M : Finset (Finset (Fin k)), IsM M ∧ ∀ f,
      (val C (k + 2 + (k + 1)) C.output f = true ↔
        ¬ (f (k + 1) = true ∨ Pr (fun u => u.val) (fun u => k + 2 + u.val) Finset.univ M f)) := by
  classical
  generalize hn : k + 2 + (k + 1) = n at hrep ⊢
  generalize ho' : C.output = o at hrep ⊢
  have ho : o < n + C.gates.length := by
    by_contra c
    have := (hrep 0 (by omega) 1 (by omega)).2 (by unfold Qc; omega)
    rw [val_out C _ _ (by omega)] at this
    exact Bool.noConfusion this
  have unx : ∀ u u', u < k + 2 → u' < k + 2 → u ∉ desc C n o → u' ∉ desc C n o → u = u' := by
    intro u u' hu hu' h1 h2
    apply rows_distinct k (by omega) u u' hu hu'
    intro v hv
    have drop : ∀ r, r ∉ desc C n o → val C n o (two r (k + 2 + v)) = val C n o (only (k + 2 + v)) := by
      intro r hr
      apply dep0
      intro i hi _
      have : i ≠ r := fun e => hr (e ▸ hi)
      simp [two, only, this]
    rw [← hrep u hu v hv, ← hrep u' hu' v hv, drop u h1, drop u' h2]
  have uny : ∀ v v', v < k + 1 → v' < k + 1 → k + 2 + v ∉ desc C n o → k + 2 + v' ∉ desc C n o → v = v' := by
    intro v v' hv hv' h1 h2
    apply cols_distinct k v v' hv hv'
    intro u hu
    have drop : ∀ r, r ∉ desc C n o → val C n o (two u r) = val C n o (only u) := by
      intro r hr
      apply dep0
      intro i hi _
      have : i ≠ r := fun e => hr (e ▸ hi)
      simp [two, only, this]
    rw [← hrep u hu v hv, ← hrep u hu v' hv', drop _ h1, drop _ h2]
  have xread := almost_all (k + 2) (fun u => u ∈ desc C n o) unx
  have yread := almost_all (k + 1) (fun v => k + 2 + v ∈ desc C n o) (fun a b ha hb => uny a b ha hb)
  have leafge : ∀ (X Y : Finset ℕ), (∀ u ∈ X, u < k + 2 ∧ u ∈ desc C n o) →
      (∀ v ∈ Y, v < k + 1 ∧ k + 2 + v ∈ desc C n o) → X.card + Y.card ≤ (leaves C n o).card := by
    intro X Y hX hY
    have e : (Y.image (fun v => k + 2 + v)).card = Y.card :=
      Finset.card_image_of_injective _ (fun a b h => by simpa using h)
    rw [← e, ← Finset.card_union_of_disjoint]
    · apply Finset.card_le_card
      intro i hi
      unfold leaves
      rw [Finset.mem_filter]
      rcases Finset.mem_union.1 hi with h | h
      · exact ⟨(hX i h).2, by have := (hX i h).1; omega⟩
      · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 h
        exact ⟨(hY v hv).2, by have := (hY v hv).1; omega⟩
    · rw [Finset.disjoint_left]
      intro i hi hi'
      obtain ⟨v, _, rfl⟩ := Finset.mem_image.1 hi'
      have := (hX _ hi).1
      omega
  have lge : 2 * k + 1 ≤ (leaves C n o).card := by
    have := leafge ((Finset.range (k + 2)).filter (fun u => u ∈ desc C n o))
      ((Finset.range (k + 1)).filter (fun v => k + 2 + v ∈ desc C n o))
      (fun u hu => by simpa using hu) (fun v hv => by simpa using hv)
    omega
  have hgl := gates_le C n o ho
  have hcnt := count C n hg o
  have hself := self_desc C n o
  have z1 : ∀ u, u < k → (k + 1 ≠ u) := fun u hu => by omega
  by_cases hnots : nots C n o = ∅
  · exfalso
    have hnn : ∀ v ∈ desc C n o, ¬ isNot C n v := by
      intro v hv h
      have : v ∈ nots C n o := Finset.mem_filter.2 ⟨hv, h⟩
      rw [hnots] at this
      exact Finset.notMem_empty _ this
    have mo := mono0 C n hg o hnn
    have xr : ∀ u < k + 1, u ∈ desc C n o := by
      intro u hu
      by_contra hu0
      have h1 : ∀ u' < k + 2, ∀ v < k + 1, Qc k u v → Qc k u' v := by
        intro u' hu' v hv hq
        have h2 := (hrep u (by omega) v hv).2 hq
        have e : val C n o (two u (k + 2 + v)) = val C n o (only (k + 2 + v)) := by
          apply dep0
          intro i hi _
          have : i ≠ u := fun e => hu0 (e ▸ hi)
          simp [two, only, this]
        rw [e] at h2
        apply (hrep u' hu' v hv).1
        exact mo _ _ (fun i hi => by
          simp only [only, two, decide_eq_true_eq] at hi ⊢
          exact Or.inr hi) h2
      by_cases d : u < k
      · obtain ⟨w, hw, hwu, _⟩ := avoid k (by omega) u u u u
        have := h1 w (by omega) w (by omega) (by unfold Qc; omega)
        unfold Qc at this
        omega
      · have := h1 0 (by omega) 0 (by omega) (by unfold Qc; omega)
        unfold Qc at this
        omega
    have yr : ∀ v < k + 1, k + 2 + v ∈ desc C n o := by
      intro v hv
      by_contra hv0
      have h1 : ∀ v' < k + 1, ∀ u < k + 2, Qc k u v → Qc k u v' := by
        intro v' hv' u hu hq
        have h2 := (hrep u hu v hv).2 hq
        have e : val C n o (two u (k + 2 + v)) = val C n o (only u) := by
          apply dep0
          intro i hi _
          have : i ≠ k + 2 + v := fun e => hv0 (e ▸ hi)
          simp [two, only, this]
        rw [e] at h2
        apply (hrep u hu v' hv').1
        exact mo _ _ (fun i hi => by
          simp only [only, two, decide_eq_true_eq] at hi ⊢
          exact Or.inl hi) h2
      obtain ⟨w, hw, hwv, _⟩ := avoid k (by omega) v v v v
      have := h1 w (by omega) w (by omega) (by unfold Qc; omega)
      unfold Qc at this
      omega
    have := leafge (Finset.range (k + 1)) (Finset.range (k + 1))
      (fun u hu => by
        rw [Finset.mem_range] at hu
        exact ⟨by omega, xr u hu⟩)
      (fun v hv => by
        rw [Finset.mem_range] at hv
        exact ⟨hv, yr v hv⟩)
    rw [Finset.card_range] at this
    have hex : (gatesIn C n o).card + 1 ≤ (leaves C n o).card + (nots C n o).card := by omega
    have H := tree_nodes C n hg o ho hex
    refine no_crown H (k := k) (by omega) (fun u => u.val) (fun u => k + 2 + u.val)
      (fun u v h => Fin.ext h) (fun u v h => Fin.ext (by omega)) (fun u v h => by have := u.isLt; omega)
      (k + 2 + k) (fun u => by have := u.isLt; omega) (fun u => by have := u.isLt; omega)
      o hself hnn ?_ ?_ ?_
    · intro u v
      change val C n o (two u.val (k + 2 + v.val)) = _
      have hu := u.isLt
      have hv := v.isLt
      rw [Bool.eq_iff_iff, hrep _ (by omega) _ (by omega), decide_eq_true_eq]
      unfold Qc
      simp only [ne_eq, Fin.ext_iff]
      omega
    · intro u
      change val C n o (two u.val (k + 2 + k)) = true
      have hu := u.isLt
      rw [hrep _ (by omega) _ (by omega)]
      unfold Qc
      omega
    · change val C n o (only (k + 2 + k)) = false
      by_contra d
      rw [Bool.not_eq_false] at d
      have := (hrep (k + 1) (by omega) k (by omega)).1 (mo _ _ (fun i hi => by
        simp only [only, two, decide_eq_true_eq] at hi ⊢
        exact Or.inr hi) d)
      unfold Qc at this
      omega
  have hpos : 0 < (nots C n o).card := Finset.card_pos.2 (Finset.nonempty_iff_ne_empty.2 hnots)
  have hex : (gatesIn C n o).card + 1 ≤ (leaves C n o).card + (nots C n o).card := by omega
  have hone : (nots C n o).card = 1 := by omega
  have H := tree_nodes C n hg o ho hex
  obtain ⟨ν, hν⟩ := Finset.card_eq_one.1 hone
  have hνm : ν ∈ nots C n o := by
    rw [hν]
    exact Finset.mem_singleton_self _
  obtain ⟨hνo, hνn⟩ := Finset.mem_filter.1 hνm
  have huni : ∀ v ∈ desc C n o, isNot C n v → v = ν := by
    intro v hv h
    have : v ∈ nots C n o := Finset.mem_filter.2 ⟨hv, h⟩
    rwa [hν, Finset.mem_singleton] at this
  have hnode : ∃ c ∈ desc C n o, c < ν ∧ desc C n ν = insert ν (desc C n c) ∧
      ∀ f, val C n ν f = !val C n c f := by
    rcases H ν hνo with ⟨h1, _⟩ | ⟨_, h, _⟩ | ⟨_, _, c, hcT, hcν, hS, hV⟩
    · have := hνn.1
      omega
    · exact absurd hνn h
    · exact ⟨c, hcT, hcν, hS, hV⟩
  obtain ⟨c, hcT, hcν, hS, hV⟩ := hnode
  have csub : ∀ i ∈ sup n (desc C n) c, i ∈ sup n (desc C n) o :=
    sup_c_sub C n o ν c H huni hcν hcT hS hνo
  have memsup : ∀ i, i ∈ sup n (desc C n) o ↔ i ∈ desc C n o ∧ i < n := fun i => Finset.mem_filter
  have pol := polar C n o ν c H huni hcν hcT hS hV o hself hνo
  have bt := bit C n o ν c H huni hcν hcT hS hV o hself hνo
  have hroot : o = ν := by
    by_contra hne
    obtain ⟨z, hzo, hzc⟩ := outside C n o ν c H huni hcν hcT hS hνo hne
    obtain ⟨i, hi⟩ := sup_ne H c hcT
    have xpos : ∀ u v : ℕ, u ∉ sup n (desc C n) c → val C n o (only (k + 2 + v)) = true →
        val C n o (two u (k + 2 + v)) = true := by
      intro u v hu h
      refine pol _ _ (fun j _ hj => ?_) (fun j hj h2 => ?_) h
      · simp only [only, two, decide_eq_true_eq] at hj ⊢
        exact Or.inr hj
      · simp only [only, two, decide_eq_true_eq] at h2 ⊢
        rcases h2 with e | e
        · exact absurd (e ▸ hj) hu
        · exact e
    have xneg : ∀ u v : ℕ, u ∈ sup n (desc C n) c → val C n o (two u (k + 2 + v)) = true →
        val C n o (only (k + 2 + v)) = true := by
      intro u v hu h
      refine pol _ _ (fun j hj h2 => ?_) (fun j _ h2 => ?_) h
      · simp only [only, two, decide_eq_true_eq] at h2 ⊢
        rcases h2 with e | e
        · exact absurd (e ▸ hu) hj
        · exact e
      · simp only [only, two, decide_eq_true_eq] at h2 ⊢
        exact Or.inr h2
    have ypos : ∀ u v : ℕ, k + 2 + v ∉ sup n (desc C n) c → val C n o (only u) = true →
        val C n o (two u (k + 2 + v)) = true := by
      intro u v hv h
      refine pol _ _ (fun j _ hj => ?_) (fun j hj h2 => ?_) h
      · simp only [only, two, decide_eq_true_eq] at hj ⊢
        exact Or.inl hj
      · simp only [only, two, decide_eq_true_eq] at h2 ⊢
        rcases h2 with e | e
        · exact e
        · exact absurd (e ▸ hj) hv
    have yneg : ∀ u v : ℕ, k + 2 + v ∈ sup n (desc C n) c → val C n o (two u (k + 2 + v)) = true →
        val C n o (only u) = true := by
      intro u v hv h
      refine pol _ _ (fun j hj h2 => ?_) (fun j _ h2 => ?_) h
      · simp only [only, two, decide_eq_true_eq] at h2 ⊢
        rcases h2 with e | e
        · exact e
        · exact absurd (e ▸ hv) hj
      · simp only [only, two, decide_eq_true_eq] at h2 ⊢
        exact Or.inl h2
    have r1 : ∀ u v : ℕ, u < k + 2 → v < k + 1 → Qc k u v → val C n o (two u (k + 2 + v)) = true :=
      fun u v hu hv h => (hrep u hu v hv).2 h
    have r0 : ∀ u : ℕ, u < k → val C n o (two u (k + 2 + u)) = false := by
      intro u hu
      rw [Bool.eq_false_iff]
      intro h
      have := (hrep u (by omega) u (by omega)).1 h
      unfold Qc at this
      omega
    have rz : ∀ v : ℕ, v < k + 1 → val C n o (two (k + 1) (k + 2 + v)) = false := by
      intro v hv
      rw [Bool.eq_false_iff]
      intro h
      have := (hrep (k + 1) (by omega) v hv).1 h
      unfold Qc at this
      omega
    have missx : ∃ m, ∀ u < k + 2, u ≠ m → u ∈ desc C n o := by
      by_cases h : ∃ m < k + 2, m ∉ desc C n o
      · obtain ⟨m, hm, hm'⟩ := h
        refine ⟨m, fun u hu hne => ?_⟩
        by_contra d
        exact hne (unx u m hu hm d hm')
      · refine ⟨0, fun u hu _ => ?_⟩
        by_contra d
        exact h ⟨u, hu, d⟩
    have missy : ∃ m, ∀ v < k + 1, v ≠ m → k + 2 + v ∈ desc C n o := by
      by_cases h : ∃ m < k + 1, k + 2 + m ∉ desc C n o
      · obtain ⟨m, hm, hm'⟩ := h
        refine ⟨m, fun v hv hne => ?_⟩
        by_contra d
        exact hne (uny v m hv hm d hm')
      · refine ⟨0, fun v hv _ => ?_⟩
        by_contra d
        exact h ⟨v, hv, d⟩
    obtain ⟨mx, hmx⟩ := missx
    obtain ⟨my, hmy⟩ := missy
    have xin : ∀ u < k, u ≠ mx → u ∈ sup n (desc C n) o := fun u hu h =>
      (memsup u).2 ⟨hmx u (by omega) h, by omega⟩
    have yin : ∀ v < k, v ≠ my → k + 2 + v ∈ sup n (desc C n) o := fun v hv h =>
      (memsup _).2 ⟨hmy v (by omega) h, by omega⟩
    have samex : ∀ u w, u < k → w < k → u ≠ w → u ∉ sup n (desc C n) c → w ∈ sup n (desc C n) c → False := by
      intro u w hu hw huw h1 h2
      have a := r1 w u (by omega) (by omega) (by unfold Qc; omega)
      have b := xpos u u h1 (xneg w u h2 a)
      rw [r0 u hu] at b
      exact Bool.noConfusion b
    have samey : ∀ v w, v < k → w < k → v ≠ w → k + 2 + v ∉ sup n (desc C n) c →
        k + 2 + w ∈ sup n (desc C n) c → False := by
      intro v w hv hw hvw h1 h2
      have a := r1 v w (by omega) (by omega) (by unfold Qc; omega)
      have b := ypos v v h1 (yneg v w h2 a)
      rw [r0 v hv] at b
      exact Bool.noConfusion b
    let px : Prop := ∃ u < k, u ≠ mx ∧ u ∈ sup n (desc C n) c
    let py : Prop := ∃ v < k, v ≠ my ∧ k + 2 + v ∈ sup n (desc C n) c
    have allx : px → ∀ u < k, u ≠ mx → u ∈ sup n (desc C n) c := by
      rintro ⟨w, hw, _, hwc⟩ u hu _
      by_contra d
      exact samex u w hu hw (fun e => d (e ▸ hwc)) d hwc
    have ally : py → ∀ v < k, v ≠ my → k + 2 + v ∈ sup n (desc C n) c := by
      rintro ⟨w, hw, _, hwc⟩ v hv _
      by_contra d
      exact samey v w hv hw (fun e => d (e ▸ hwc)) d hwc
    have nox : ¬ px → ∀ u < k, u ∉ sup n (desc C n) c := by
      intro h u hu d
      have : u ≠ mx := by
        intro e
        have h1 := (memsup u).1 (csub u d)
        have h2 : ∃ w < k, w ≠ mx := by
          obtain ⟨w, hw, hwm, _⟩ := avoid k (by omega) mx mx mx mx
          exact ⟨w, hw, hwm⟩
        obtain ⟨w, hw, hwm⟩ := h2
        have hwc : w ∉ sup n (desc C n) c := fun e' => h ⟨w, hw, hwm, e'⟩
        exact samex w u hw hu (by omega) hwc d
      exact h ⟨u, hu, this, d⟩
    have noy : ¬ py → ∀ v < k, k + 2 + v ∉ sup n (desc C n) c := by
      intro h v hv d
      have : v ≠ my := by
        intro e
        obtain ⟨w, hw, hwm, _⟩ := avoid k (by omega) my my my my
        have hwc : k + 2 + w ∉ sup n (desc C n) c := fun e' => h ⟨w, hw, hwm, e'⟩
        exact samey w v hw hv (by omega) hwc d
      exact h ⟨v, hv, this, d⟩
    have zform : ∀ j, j ∈ sup n (desc C n) o → j < k + 2 ∨ ∃ v < k + 1, j = k + 2 + v := by
      intro j hj
      have := ((memsup j).1 hj).2
      by_cases d : j < k + 2
      · exact Or.inl d
      · exact Or.inr ⟨j - (k + 2), by omega, by omega⟩
    have cread : ∀ j, j ∈ sup n (desc C n) o → j ∈ desc C n o := fun j hj => ((memsup j).1 hj).1
    by_cases hpx : px <;> by_cases hpy : py
    · have z0 : ∀ j < k + 1, val C n o (only (k + 2 + j)) = true := by
        intro j hj
        obtain ⟨w, hw, hwm, hwj, _⟩ := avoid k (by omega) mx j j j
        exact xneg w j (allx hpx w hw hwm) (r1 w j (by omega) hj (by unfold Qc; omega))
      have c0 : ∀ i < k + 2, i ≠ k + 1 → val C n o (only i) = true := by
        intro i hi hik
        obtain ⟨w, hw, hwm, hwi, _⟩ := avoid k (by omega) my i i i
        exact yneg i w (ally hpy w hw hwm) (r1 i w hi (by omega) (by unfold Qc; omega))
      rcases zform z hzo with hz | ⟨t, ht, rfl⟩
      · by_cases d : z < k
        · by_cases e : z = mx
          · obtain ⟨w, hw, hwm, _⟩ := avoid k (by omega) mx mx mx mx
            exact samex z w d hw (by omega) hzc (allx hpx w hw hwm)
          · exact hzc (allx hpx z d e)
        by_cases e : z = k
        · subst e
          have row : mx = z := by
            have hmxlt : mx < z + 2 := by
              by_contra g
              have h1 : ∀ u < z + 2, u ∈ desc C n o := fun u hu => hmx u hu (by omega)
              have := leafge (Finset.range (z + 2))
                ((Finset.range (z + 1)).filter (fun v => z + 2 + v ∈ desc C n o))
                (fun u hu => by
                  rw [Finset.mem_range] at hu
                  exact ⟨hu, h1 u hu⟩)
                (fun v hv => by simpa using hv)
              rw [Finset.card_range] at this
              omega
            by_cases g : mx ∈ desc C n o
            · have h1 : ∀ u < z + 2, u ∈ desc C n o := fun u hu => by
                by_cases e : u = mx
                · exact e ▸ g
                · exact hmx u hu e
              have := leafge (Finset.range (z + 2))
                ((Finset.range (z + 1)).filter (fun v => z + 2 + v ∈ desc C n o))
                (fun u hu => by
                  rw [Finset.mem_range] at hu
                  exact ⟨hu, h1 u hu⟩)
                (fun v hv => by simpa using hv)
              rw [Finset.card_range] at this
              omega
            apply rows_distinct z (by omega) mx z hmxlt (by omega)
            intro v hv
            have e1 : val C n o (two mx (z + 2 + v)) = val C n o (only (z + 2 + v)) := by
              apply dep0
              intro i hi _
              have : i ≠ mx := fun e => g (e ▸ hi)
              simp [two, only, this]
            rw [← hrep mx hmxlt v hv, ← hrep z (by omega) v hv, e1, z0 v hv,
              r1 z v (by omega) hv (by unfold Qc; omega)]
          obtain ⟨g1, _⟩ := (memsup z).1 hzo
          have : ∀ u < z + 2, u ∈ desc C n o := fun u hu => by
            by_cases e : u = z
            · exact e ▸ g1
            · exact hmx u hu (by omega)
          have := leafge (Finset.range (z + 2))
            ((Finset.range (z + 1)).filter (fun v => z + 2 + v ∈ desc C n o))
            (fun u hu => by
              rw [Finset.mem_range] at hu
              exact ⟨hu, this u hu⟩)
            (fun v hv => by simpa using hv)
          rw [Finset.card_range] at this
          omega
        have ez : z = k + 1 := by omega
        have a := xpos z 0 hzc (z0 0 (by omega))
        rw [ez, rz 0 (by omega)] at a
        exact Bool.noConfusion a
      · by_cases d : t < k
        · by_cases e : t = my
          · obtain ⟨w, hw, hwm, _⟩ := avoid k (by omega) my my my my
            exact samey t w d hw (by omega) hzc (ally hpy w hw hwm)
          · exact hzc (ally hpy t d e)
        have et : t = k := by omega
        subst et
        have col : ∀ i < t + 2, (val C n o (only i) = true ↔ Qc t i t) := by
          intro i hi
          by_cases e : i = t + 1
          · have hf : val C n o (only i) = false := by
              rw [Bool.eq_false_iff]
              intro h
              have a := ypos i t hzc h
              rw [e, rz t (by omega)] at a
              exact Bool.noConfusion a
            rw [hf]
            unfold Qc
            simp [e]
          · rw [c0 i hi e]
            unfold Qc
            exact ⟨fun _ => by omega, fun _ => rfl⟩
        have g1 := cread _ hzo
        have miss : ∃ v < t + 1, t + 2 + v ∉ desc C n o := by
          by_contra g
          have h1 : ∀ v < t + 1, t + 2 + v ∈ desc C n o := fun v hv => by
            by_contra d'
            exact g ⟨v, hv, d'⟩
          have := leafge ((Finset.range (t + 2)).filter (fun u => u ∈ desc C n o)) (Finset.range (t + 1))
            (fun u hu => by simpa using hu)
            (fun v hv => by
              rw [Finset.mem_range] at hv
              exact ⟨hv, h1 v hv⟩)
          rw [Finset.card_range] at this
          omega
        obtain ⟨m, hm, hm'⟩ := miss
        have : m = t := by
          apply cols_distinct t m t hm (by omega)
          intro u hu
          have e1 : val C n o (two u (t + 2 + m)) = val C n o (only u) := by
            apply dep0
            intro i hi _
            have : i ≠ t + 2 + m := fun e => hm' (e ▸ hi)
            simp [two, only, this]
          rw [← hrep u hu m hm, e1, col u hu]
        exact hm' (this ▸ g1)
    · obtain ⟨a, ha, ham, _⟩ := avoid k (by omega) mx mx mx mx
      obtain ⟨b, hb, hbm, hba, _⟩ := avoid k (by omega) mx a a a
      obtain ⟨d, hd, hdm, hda, hdb, _⟩ := avoid k (by omega) mx a b b
      have ync : ∀ j < k, k + 2 + j ∉ sup n (desc C n) c := noy hpy
      have eqc : ∀ u j, j < k → val C n c (two u (k + 2 + j)) = val C n c (only u) := by
        intro u j hj
        apply dep H c hcT
        intro i hi
        have : i ≠ k + 2 + j := fun e => ync j hj (e ▸ hi)
        simp [two, only, this]
      have pig : ∀ u w, u < k → w < k → u ≠ w → u ≠ mx → w ≠ mx →
          val C n c (only u) = val C n c (only w) → False := by
        intro u w hu hw huw hum hwm h
        have uc := allx hpx u hu hum
        have wc := allx hpx w hw hwm
        have key : val C n o (two u (k + 2 + u)) = val C n o (two w (k + 2 + u)) := by
          apply bt
          · intro i hi
            have e1 : i ≠ u := fun e => hi (e ▸ uc)
            have e2 : i ≠ w := fun e => hi (e ▸ wc)
            simp [two, e1, e2]
          · rw [eqc u u hu, eqc w u hu, h]
        rw [r0 u hu, r1 w u (by omega) (by omega) (by unfold Qc; omega)] at key
        exact Bool.noConfusion key
      have three : ∀ p q r : Bool, p = q ∨ p = r ∨ q = r := by decide
      rcases three (val C n c (only a)) (val C n c (only b)) (val C n c (only d)) with h | h | h
      · exact pig a b ha hb hba.symm ham hbm h
      · exact pig a d ha hd hda.symm ham hdm h
      · exact pig b d hb hd hdb.symm hbm hdm h
    · obtain ⟨a, ha, ham, _⟩ := avoid k (by omega) my my my my
      obtain ⟨b, hb, hbm, hba, _⟩ := avoid k (by omega) my a a a
      obtain ⟨d, hd, hdm, hda, hdb, _⟩ := avoid k (by omega) my a b b
      have xnc : ∀ j < k, j ∉ sup n (desc C n) c := nox hpx
      have eqc : ∀ v j, j < k → val C n c (two j (k + 2 + v)) = val C n c (only (k + 2 + v)) := by
        intro v j hj
        apply dep H c hcT
        intro i hi
        have : i ≠ j := fun e => xnc j hj (e ▸ hi)
        simp [two, only, this]
      have pig : ∀ u w, u < k → w < k → u ≠ w → u ≠ my → w ≠ my →
          val C n c (only (k + 2 + u)) = val C n c (only (k + 2 + w)) → False := by
        intro u w hu hw huw hum hwm h
        have uc := ally hpy u hu hum
        have wc := ally hpy w hw hwm
        have key : val C n o (two u (k + 2 + u)) = val C n o (two u (k + 2 + w)) := by
          apply bt
          · intro i hi
            have e1 : i ≠ k + 2 + u := fun e => hi (e ▸ uc)
            have e2 : i ≠ k + 2 + w := fun e => hi (e ▸ wc)
            simp [two, e1, e2]
          · rw [eqc u u hu, eqc w u hu, h]
        rw [r0 u hu, r1 u w (by omega) (by omega) (by unfold Qc; omega)] at key
        exact Bool.noConfusion key
      have three : ∀ p q r : Bool, p = q ∨ p = r ∨ q = r := by decide
      rcases three (val C n c (only (k + 2 + a))) (val C n c (only (k + 2 + b)))
          (val C n c (only (k + 2 + d))) with h | h | h
      · exact pig a b ha hb hba.symm ham hbm h
      · exact pig a d ha hd hda.symm ham hdm h
      · exact pig b d hb hd hdb.symm hbm hdm h
    · have xnc : ∀ j < k, j ∉ sup n (desc C n) c := nox hpx
      have ync : ∀ j < k, k + 2 + j ∉ sup n (desc C n) c := noy hpy
      have nk : k ∉ sup n (desc C n) c := by
        intro h
        obtain ⟨j, hj, hjm, _⟩ := avoid k (by omega) mx mx mx mx
        have a := xneg k j h (r1 k j (by omega) (by omega) (by unfold Qc; omega))
        have b := xpos j j (xnc j hj) a
        rw [r0 j hj] at b
        exact Bool.noConfusion b
      have nyk : k + 2 + k ∉ sup n (desc C n) c := by
        intro h
        obtain ⟨j, hj, hjm, _⟩ := avoid k (by omega) my my my my
        have a := yneg j k h (r1 j k (by omega) (by omega) (by unfold Qc; omega))
        have b := ypos j j (ync j hj) a
        rw [r0 j hj] at b
        exact Bool.noConfusion b
      have hik : i = k + 1 := by
        rcases zform i (csub i hi) with h | ⟨t, ht, rfl⟩
        · by_cases d : i < k
          · exact absurd hi (xnc i d)
          by_cases e : i = k
          · exact absurd (e ▸ hi) nk
          omega
        · by_cases d : t < k
          · exact absurd hi (ync t d)
          have : t = k := by omega
          exact absurd (this ▸ hi) nyk
      have g1 := cread _ (csub i hi)
      rw [hik] at g1
      have z0 : ∀ j < k, j ≠ mx → val C n o (only (k + 2 + j)) = false := by
        intro j hj hjm
        rw [Bool.eq_false_iff]
        intro h
        have a := xpos j j (xnc j hj) h
        rw [r0 j hj] at a
        exact Bool.noConfusion a
      have miss : ∃ m < k + 2, m ∉ desc C n o := by
        by_contra g
        have h1 : ∀ u < k + 2, u ∈ desc C n o := fun u hu => by
          by_contra d'
          exact g ⟨u, hu, d'⟩
        have := leafge (Finset.range (k + 2))
          ((Finset.range (k + 1)).filter (fun v => k + 2 + v ∈ desc C n o))
          (fun u hu => by
            rw [Finset.mem_range] at hu
            exact ⟨hu, h1 u hu⟩)
          (fun v hv => by simpa using hv)
        rw [Finset.card_range] at this
        omega
      obtain ⟨m, hm, hm'⟩ := miss
      have mrow : ∀ v < k + 1, (val C n o (only (k + 2 + v)) = true ↔ Qc k m v) := by
        intro v hv
        have e1 : val C n o (two m (k + 2 + v)) = val C n o (only (k + 2 + v)) := by
          apply dep0
          intro i hi _
          have : i ≠ m := fun e => hm' (e ▸ hi)
          simp [two, only, this]
        rw [← e1, hrep m hm v hv]
      have mne : m ≠ k + 1 := fun e => hm' (e ▸ g1)
      by_cases d : m < k
      · obtain ⟨j, hj, hjm, hjm', _⟩ := avoid k (by omega) mx m m m
        have a := (mrow j (by omega)).2 (by unfold Qc; omega)
        rw [z0 j hj hjm] at a
        exact Bool.noConfusion a
      · obtain ⟨j, hj, hjm, _⟩ := avoid k (by omega) mx mx mx mx
        have a := (mrow j (by omega)).2 (by unfold Qc; omega)
        rw [z0 j hj hjm] at a
        exact Bool.noConfusion a
  subst hroot
  have hFG : ∀ f, val C n o f = !val C n c f := hV
  have cmon : ∀ v ∈ desc C n c, ¬ isNot C n v := fun v hv =>
    below_c C n o o c huni hcν v hv (desc_trans C n o c hcT hv)
  have supc : sup n (desc C n) c = sup n (desc C n) o := (sup_un hS hνn.1).symm
  have mc := mono H c hcT cmon
  have G : ∀ u < k + 2, ∀ v < k + 1, (val C n c (two u (k + 2 + v)) = true ↔ ¬ Qc k u v) := by
    intro u hu v hv
    rw [← hrep u hu v hv, hFG]
    cases val C n c (two u (k + 2 + v)) <;> simp
  have notin : ∀ i, i < n → i ∉ desc C n o → i ∉ sup n (desc C n) c := by
    intro i _ h d
    rw [supc] at d
    exact h ((memsup i).1 d).1
  have gdrop : ∀ r s, r ∉ sup n (desc C n) c → val C n c (two r s) = val C n c (only s) := by
    intro r s hr
    apply dep H c hcT
    intro i hi
    have : i ≠ r := fun e => hr (e ▸ hi)
    simp [two, only, this]
  have gdrop' : ∀ r s, s ∉ sup n (desc C n) c → val C n c (two r s) = val C n c (only r) := by
    intro r s hs
    apply dep H c hcT
    intro i hi
    have : i ≠ s := fun e => hs (e ▸ hi)
    simp [two, only, this]
  have up1 : ∀ a b, val C n c (only a) = true → val C n c (two a b) = true := fun a b h =>
    mc _ _ (fun i hi => by
      simp only [only, two, decide_eq_true_eq] at hi ⊢
      exact Or.inl hi) h
  have up2 : ∀ a b, val C n c (only b) = true → val C n c (two a b) = true := fun a b h =>
    mc _ _ (fun i hi => by
      simp only [only, two, decide_eq_true_eq] at hi ⊢
      exact Or.inr hi) h
  have xk : ∃ m < k + 2, m ∉ desc C n o := by
    by_contra g
    have h1 : ∀ u < k + 2, u ∈ desc C n o := fun u hu => by
      by_contra d'
      exact g ⟨u, hu, d'⟩
    have := leafge (Finset.range (k + 2))
      ((Finset.range (k + 1)).filter (fun v => k + 2 + v ∈ desc C n o))
      (fun u hu => by
        rw [Finset.mem_range] at hu
        exact ⟨hu, h1 u hu⟩)
      (fun v hv => by simpa using hv)
    rw [Finset.card_range] at this
    omega
  have yk : ∃ m < k + 1, k + 2 + m ∉ desc C n o := by
    by_contra g
    have h1 : ∀ v < k + 1, k + 2 + v ∈ desc C n o := fun v hv => by
      by_contra d'
      exact g ⟨v, hv, d'⟩
    have := leafge ((Finset.range (k + 2)).filter (fun u => u ∈ desc C n o)) (Finset.range (k + 1))
      (fun u hu => by simpa using hu)
      (fun v hv => by
        rw [Finset.mem_range] at hv
        exact ⟨hv, h1 v hv⟩)
    rw [Finset.card_range] at this
    omega
  obtain ⟨mx, hmx, hmx'⟩ := xk
  obtain ⟨my, hmy, hmy'⟩ := yk
  have emx : mx = k := by
    have hz : ∀ v < k + 1, ¬ Qc k mx v → ¬ Qc k k v := by
      intro v hv h
      have a := (G mx hmx v hv).2 h
      rw [gdrop _ _ (notin mx (by omega) hmx')] at a
      exact (G k (by omega) v hv).1 (up2 k _ a)
    have allq : ∀ v < k + 1, Qc k mx v := by
      intro v hv
      by_contra d
      apply hz v hv d
      unfold Qc
      omega
    by_contra d
    by_cases e : mx < k
    · have := allq mx (by omega)
      unfold Qc at this
      omega
    · have := allq 0 (by omega)
      unfold Qc at this
      omega
  have emy : my = k := by
    by_contra d
    have hmyk : my < k := by omega
    have a := (G my (by omega) my hmy).2 (by unfold Qc; omega)
    rw [gdrop' _ _ (notin _ (by omega) hmy')] at a
    obtain ⟨w, hw, hwm, _⟩ := avoid k (by omega) my my my my
    have b := (G my (by omega) w (by omega)).1 (up1 my _ a)
    apply b
    unfold Qc
    omega
  subst mx
  subst my
  have xin : ∀ u < k + 2, u ≠ k → u ∈ desc C n o := fun u hu h => by
    by_contra d
    exact h (unx u k hu (by omega) d hmx')
  have yin : ∀ v < k, k + 2 + v ∈ desc C n o := fun v hv => by
    by_contra d
    have := uny v k (by omega) (by omega) d hmy'
    omega
  have hsupc : ∀ i, i ∈ sup n (desc C n) c ↔
      i = k + 1 ∨ ∃ u ∈ (Finset.univ : Finset (Fin k)), i = u.val ∨ i = k + 2 + u.val := by
    intro i
    rw [supc, memsup]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases d : i < k
      · exact Or.inr ⟨⟨i, d⟩, Finset.mem_univ _, Or.inl rfl⟩
      by_cases e : i = k
      · exact absurd (e ▸ h1) hmx'
      by_cases f : i = k + 1
      · exact Or.inl f
      by_cases g : i = k + 2 + k
      · exact absurd (g ▸ h1) hmy'
      exact Or.inr ⟨⟨i - (k + 2), by omega⟩, Finset.mem_univ _,
        Or.inr (show i = k + 2 + (i - (k + 2)) by omega)⟩
    · rintro (rfl | ⟨u, _, rfl | rfl⟩)
      · exact ⟨xin _ (by omega) (by omega), by omega⟩
      · have := u.isLt
        exact ⟨xin _ (by omega) (by omega), by omega⟩
      · have := u.isLt
        exact ⟨yin _ this, by omega⟩
  have notk : k + 2 + k ∉ sup n (desc C n) c := notin _ (by omega) hmy'
  have zk : val C n c (only (k + 1)) = true := by
    have a := (G (k + 1) (by omega) k (by omega)).2 (by unfold Qc; omega)
    rwa [gdrop' _ _ notk] at a
  have core0 : ∀ i, i ≠ k + 1 → val C n c (only i) = false := by
    intro i hi
    by_cases d : i ∈ sup n (desc C n) c
    swap
    · apply off H hcT cmon
      intro j hj
      have : j ≠ i := fun e => d (e ▸ hj)
      simp [only, this]
    rcases (hsupc i).1 d with e | ⟨u, _, e | e⟩
    · exact absurd e hi
    · have hu := u.isLt
      rw [Bool.eq_false_iff]
      intro h
      obtain ⟨w, hw, hwu, _⟩ := avoid k (by omega) u.val u.val u.val u.val
      have := (G u.val (by omega) w (by omega)).1 (up1 _ _ (e ▸ h))
      apply this
      unfold Qc
      omega
    · have hu := u.isLt
      rw [Bool.eq_false_iff]
      intro h
      obtain ⟨w, hw, hwu, _⟩ := avoid k (by omega) u.val u.val u.val u.val
      have := (G w (by omega) u.val (by omega)).1 (up2 _ _ (e ▸ h))
      apply this
      unfold Qc
      omega
  obtain ⟨M, hM, _, hv⟩ := cls_z H (fun u : Fin k => u.val) (fun u : Fin k => k + 2 + u.val)
    (fun u v h => Fin.ext h) (fun u v h => Fin.ext (by omega)) (fun u v h => by have := u.isLt; omega)
    (k + 1) (fun u => by have := u.isLt; omega) (fun u => by have := u.isLt; omega)
    c hcT cmon Finset.univ hsupc (by
      intro u _ v _
      change val C n c (two u.val (k + 2 + v.val)) = _
      have hu := u.isLt
      have hv := v.isLt
      rw [Bool.eq_iff_iff, G _ (by omega) _ (by omega), decide_eq_true_eq, Fin.ext_iff]
      unfold Qc
      omega) core0 zk
  refine ⟨M, hM, fun f => ?_⟩
  rw [hFG, ← hv]
  change (!val C n c f) = true ↔ ¬ val C n c f = true
  cases val C n c f <;> simp

section build

variable (nr : ℕ) {k : ℕ}

def term (b : Fin k × Fin k) (f : ℕ → Bool) : Bool :=
  if b.1 = b.2 then f b.1.val && f (nr + b.1.val)
  else (f b.1.val || f (nr + b.2.val)) && (f b.2.val || f (nr + b.1.val))

def blk (m : ℕ) (b : Fin k × Fin k) : List Gate × ℕ :=
  if b.1 = b.2 then ([⟨GateOp.and, [b.1.val, nr + b.1.val]⟩], m)
  else ([⟨GateOp.or, [b.1.val, nr + b.2.val]⟩, ⟨GateOp.or, [b.2.val, nr + b.1.val]⟩,
    ⟨GateOp.and, [m, m + 1]⟩], m + 2)

def bcost (b : Fin k × Fin k) : ℕ := if b.1 = b.2 then 2 else 4

def build (n : ℕ) : List (Fin k × Fin k) → List Gate × ℕ
  | [] => ([], 0)
  | [b] => blk nr n b
  | b :: b' :: l =>
    let r := build n (b' :: l)
    let s := blk nr (n + r.1.length) b
    (r.1 ++ s.1 ++ [⟨GateOp.or, [r.2, s.2]⟩], n + r.1.length + s.1.length)

def Mon (gs : List Gate) : Prop := ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

theorem run_one (g : Gate) (w : List Bool) : run [g] w = step w g := rfl

theorem blk_ok (n : ℕ) (hn : ∀ u : Fin k, u.val < n ∧ nr + u.val < n) (f : ℕ → Bool) (w : List Bool)
    (hlen : n ≤ w.length) (hf : ∀ i < n, w.getD i false = f i) (b : Fin k × Fin k) :
    (run (blk nr w.length b).1 w).getD (blk nr w.length b).2 false = term nr b f ∧
    (blk nr w.length b).2 < w.length + (blk nr w.length b).1.length ∧
    (blk nr w.length b).1.length + 1 = bcost b ∧ Mon (blk nr w.length b).1 := by
  have a1 := hn b.1
  have a2 := hn b.2
  have keep : ∀ (t : List Bool) (i : ℕ), i < n → (w ++ t).getD i false = f i := by
    intro t i hi
    rw [getD_keep _ _ (by omega)]
    exact hf i hi
  by_cases h : b.1 = b.2
  · simp only [blk, term, bcost, if_pos h]
    refine ⟨?_, by simp, by simp, ?_⟩
    · rw [run_one]
      simp only [step]
      rw [getD_new _ _ rfl]
      simp [GateOp.eval, ← List.getD_eq_getElem?_getD, hf _ a1.1, hf _ a1.2]
    · intro g hg
      rw [List.mem_singleton] at hg
      subst hg
      simp
  · simp only [blk, term, bcost, if_neg h]
    refine ⟨?_, by simp, by simp, ?_⟩
    · have s1 : step w ⟨GateOp.or, [b.1.val, nr + b.2.val]⟩ = w ++ [f b.1.val || f (nr + b.2.val)] := by
        simp only [step, List.map_cons, List.map_nil, hf _ a1.1, hf _ a2.2]
        simp [GateOp.eval]
      have s2 : ∀ x : Bool, step (w ++ [x]) ⟨GateOp.or, [b.2.val, nr + b.1.val]⟩ =
          w ++ [x] ++ [f b.2.val || f (nr + b.1.val)] := by
        intro x
        simp only [step, List.map_cons, List.map_nil, keep _ _ a2.1, keep _ _ a1.2]
        simp [GateOp.eval]
      have s3 : ∀ x y : Bool, step (w ++ [x] ++ [y]) ⟨GateOp.and, [w.length, w.length + 1]⟩ =
          w ++ [x] ++ [y] ++ [x && y] := by
        intro x y
        have e1 : (w ++ [x] ++ [y]).getD w.length false = x := by
          rw [getD_keep _ _ (by simp), getD_new _ _ rfl]
        have e2 : (w ++ [x] ++ [y]).getD (w.length + 1) false = y := getD_new _ _ (by simp)
        simp only [step, List.map_cons, List.map_nil, e1, e2]
        simp [GateOp.eval]
      rw [run_cons, s1, run_cons, s2, run_cons, s3, run_nil]
      exact getD_new _ _ (by simp)
    · intro g hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl <;> simp

theorem build_ok (n : ℕ) (hn : ∀ u : Fin k, u.val < n ∧ nr + u.val < n) (f : ℕ → Bool) (w : List Bool)
    (hlen : w.length = n) (hf : ∀ i < n, w.getD i false = f i) :
    ∀ l : List (Fin k × Fin k), l ≠ [] →
      (run (build nr n l).1 w).getD (build nr n l).2 false = l.any (fun b => term nr b f) ∧
      (build nr n l).2 < n + (build nr n l).1.length ∧
      (build nr n l).1.length + 1 = (l.map bcost).sum ∧ Mon (build nr n l).1 := by
  intro l
  induction l with
  | nil => exact fun h => absurd rfl h
  | cons b l ih =>
    intro _
    cases l with
    | nil =>
      have := blk_ok nr n hn f w (by omega) hf b
      rw [hlen] at this
      simpa [build] using this
    | cons b' l =>
      obtain ⟨h1, h2, h3, h4⟩ := ih (by simp)
      simp only [build]
      generalize hr : build nr n (b' :: l) = r at h1 h2 h3 h4
      let w1 := run r.1 w
      have l1 : w1.length = n + r.1.length := by
        simp only [w1, run_length, hlen]
      have hf1 : ∀ i < n, w1.getD i false = f i := by
        intro i hi
        simp only [w1]
        rw [prefix_keep _ _ (by omega)]
        exact hf i hi
      obtain ⟨k1, k2, k3, k4⟩ := blk_ok nr n hn f w1 (by omega) hf1 b
      rw [l1] at k1 k2 k3 k4
      generalize hs : blk nr (n + r.1.length) b = s at k1 k2 k3 k4
      let w2 := run s.1 w1
      have l2 : w2.length = n + r.1.length + s.1.length := by
        simp only [w2, run_length, l1]
      have keep : w2.getD r.2 false = w1.getD r.2 false := by
        simp only [w2]
        exact prefix_keep _ _ (by omega)
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [run_append, run_append, run_one]
        change (step w2 ⟨GateOp.or, [r.2, s.2]⟩).getD (n + r.1.length + s.1.length) false = _
        simp only [step]
        rw [getD_new _ _ l2.symm]
        simp only [List.map_cons, List.map_nil]
        rw [keep]
        change GateOp.or.eval [w1.getD r.2 false, (run s.1 w1).getD s.2 false] = _
        rw [show w1.getD r.2 false = _ from h1, k1, List.any_cons (a := b)]
        simp [GateOp.eval, Bool.or_comm]
      · simp only [List.length_append, List.length_singleton]
        omega
      · rw [List.map_cons, List.sum_cons]
        simp only [List.length_append, List.length_singleton]
        omega
      · intro g hg
        simp only [List.mem_append, List.mem_singleton] at hg
        rcases hg with (hg | hg) | hg
        · exact h4 g hg
        · exact k4 g hg
        · subst hg
          simp

theorem blocks (nr : ℕ) (M : Finset (Finset (Fin k))) (hM : IsM M) :
    ∃ l : List (Fin k × Fin k), (l.map bcost).sum = 2 * k ∧
      ∀ f, (l.any (fun b => term nr b f) = true ↔
        Pr (fun u => u.val) (fun u => nr + u.val) Finset.univ M f) := by
  have pairs : ∀ M : Finset (Finset (Fin k)), IsM M → ∃ l : List (Fin k × Fin k),
      (l.map bcost).sum = 2 * (M.biUnion id).card ∧
      ∀ f, (l.any (fun b => term nr b f) = true ↔
        Pr (fun u => u.val) (fun u => nr + u.val) (M.biUnion id) M f) := by
    intro M
    induction M using Finset.induction_on with
    | empty => exact fun _ => ⟨[], by simp, fun f => by simp [Pr]⟩
    | @insert e M he ih =>
      intro hM
      obtain ⟨l, h1, h2⟩ := ih (hM.mono (Finset.subset_insert _ _))
      obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 (hM.1 e (Finset.mem_insert_self _ _))
      have hdj : Disjoint ({a, b} : Finset (Fin k)) (M.biUnion id) := by
        rw [Finset.disjoint_biUnion_right]
        intro g hg
        exact hM.2 _ (Finset.mem_insert_self _ _) g (Finset.mem_insert_of_mem hg) (fun c => he (c ▸ hg))
      refine ⟨(a, b) :: l, ?_, fun f => ?_⟩
      · rw [List.map_cons, List.sum_cons, h1, Finset.biUnion_insert, id,
          Finset.card_union_of_disjoint hdj, Finset.card_pair hab]
        simp only [bcost, if_neg hab]
        omega
      · rw [List.any_cons, Bool.or_eq_true, h2, Finset.biUnion_insert, id]
        have e1 : insert ({a, b} : Finset (Fin k)) M = {{a, b}} ∪ M := Finset.insert_eq _ _
        rw [e1, Pr_union]
        apply or_congr _ Iff.rfl
        simp only [term, if_neg hab, Pr, Finset.mem_insert, Finset.mem_singleton, or_and_right,
          exists_or, exists_eq_left, forall_eq_or_imp, forall_eq, Bool.and_eq_true, Bool.or_eq_true]
        tauto
  obtain ⟨l, h1, h2⟩ := pairs M hM
  let R := Finset.univ \ M.biUnion id
  refine ⟨l ++ R.toList.map (fun u => (u, u)), ?_, fun f => ?_⟩
  · have : (R.toList.map (fun u => (u, u))).map bcost = List.replicate R.card 2 := by
      rw [List.map_map, ← Finset.length_toList, ← List.map_const']
      apply List.map_congr_left
      intro u _
      simp [bcost]
    rw [List.map_append, List.sum_append, h1, this, List.sum_replicate, smul_eq_mul]
    have h3 := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (M.biUnion id))
    rw [Finset.card_univ, Fintype.card_fin] at h3
    simp only [R]
    omega
  · rw [List.any_append, Bool.or_eq_true, h2]
    have hu : M.biUnion id ∪ R = Finset.univ := by
      simp [R]
    have e : Pr (fun u => u.val) (fun u => nr + u.val) Finset.univ M f ↔
        Pr (fun u => u.val) (fun u => nr + u.val) (M.biUnion id) M f ∨
        Pr (fun u => u.val) (fun u => nr + u.val) R ∅ f := by
      rw [← Pr_union, hu, Finset.union_empty]
    rw [e]
    apply or_congr Iff.rfl
    simp [Pr, term, List.any_map, List.any_eq_true]

end build

theorem list_inp (l : List Bool) (n : ℕ) (h : l.length = n) : l = inp n (fun i => l.getD i false) := by
  apply List.ext_getElem
  · simp [inp, h]
  · intro i h1 h2
    simp [inp, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]

theorem getD_app_left {a b : ℕ} (x : Fin a → Bool) (y : Fin b → Bool) (i : ℕ) (hi : i < a) :
    (List.ofFn x ++ List.ofFn y).getD i false = x ⟨i, hi⟩ := by
  rw [getD_keep _ _ (by simpa using hi)]
  simp [List.getD_eq_getElem?_getD, hi]

theorem getD_app_right {a b : ℕ} (x : Fin a → Bool) (y : Fin b → Bool) (i : ℕ) (hi : i < b) :
    (List.ofFn x ++ List.ofFn y).getD (a + i) false = y ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
  simp [hi]

theorem oneEach_inp {a b : ℕ} (u : Fin a) (v : Fin b) :
    PEqualNP.Represents.oneEach u v = inp (a + b) (two u.val (a + v.val)) := by
  apply List.ext_getElem
  · simp [PEqualNP.Represents.oneEach, inp]
  · intro i h1 h2
    have hi : i < a + b := by simpa [inp] using h2
    have key : (PEqualNP.Represents.oneEach u v).getD i false = two u.val (a + v.val) i := by
      unfold PEqualNP.Represents.oneEach two
      have hu := u.isLt
      have hv := v.isLt
      by_cases d : i < a
      · rw [getD_app_left _ _ i d]
        rw [decide_eq_decide, Fin.ext_iff]
        simp only
        omega
      · have e : i = a + (i - a) := by omega
        conv_lhs => rw [e]
        rw [getD_app_right _ _ (i - a) (by omega)]
        rw [decide_eq_decide, Fin.ext_iff]
        simp only
        omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, Option.getD_some] at key
    rw [key]
    simp [inp]

open PEqualNP.MetaComplexity PEqualNP.Represents

theorem pr_point (k d u v : ℕ) (hkd : k ≤ d) (hu : u < d) (M : Finset (Finset (Fin k))) (hM : IsM M) :
    Pr (fun w => w.val) (fun w => d + w.val) Finset.univ M (two u (d + v)) ↔ u = v ∧ u < k := by
  constructor
  · rintro (⟨w, _, h1, h2⟩ | ⟨e, he, h⟩)
    · simp only [two, decide_eq_true_eq] at h1 h2
      have := w.isLt
      omega
    · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 (hM.1 e he)
      have hne : a.val ≠ b.val := fun c => hab (Fin.ext c)
      have ha := a.isLt
      have hb := b.isLt
      simp only [two, decide_eq_true_eq, Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp,
        forall_eq] at h
      omega
  · rintro ⟨h, hk⟩
    left
    refine ⟨⟨u, hk⟩, Finset.mem_univ _, by simp [two], by simp [two, h]⟩

theorem pr_pred (k nr nc : ℕ) (h1 : k ≤ nr) (h2 : k ≤ nc) (x : Fin nr → Bool) (y : Fin nc → Bool)
    (M : Finset (Finset (Fin k))) (hM : IsM M) :
    Pr (fun w => w.val) (fun w => nr + w.val) Finset.univ M (fun i => (List.ofFn x ++ List.ofFn y).getD i false) ↔
      (Finset.univ.filter (fun i : Fin k => (List.ofFn x).getD i.val false = true) ∩
        Finset.univ.filter (fun i : Fin k => (List.ofFn y).getD i.val false = true)).Nonempty ∨
      (M ∩ Finset.univ.filter (fun e : Finset (Fin k) => e.card = 2 ∧
        (e ⊆ Finset.univ.filter (fun i : Fin k => (List.ofFn x).getD i.val false = true) ∨
         e ⊆ Finset.univ.filter (fun i : Fin k => (List.ofFn y).getD i.val false = true)))).Nonempty := by
  have ex : ∀ w : Fin k, (List.ofFn x ++ List.ofFn y).getD w.val false = (List.ofFn x).getD w.val false := by
    intro w
    have := w.isLt
    exact getD_keep _ _ (by rw [List.length_ofFn]; omega)
  have ey : ∀ w : Fin k, (List.ofFn x ++ List.ofFn y).getD (nr + w.val) false =
      (List.ofFn y).getD w.val false := by
    intro w
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp), List.getD_eq_getElem?_getD]
    simp
  unfold Pr
  apply or_congr
  · constructor
    · rintro ⟨w, _, a, b⟩
      exact ⟨w, Finset.mem_inter.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, (ex w).symm.trans a⟩,
        Finset.mem_filter.2 ⟨Finset.mem_univ _, (ey w).symm.trans b⟩⟩⟩
    · rintro ⟨w, hw⟩
      rw [Finset.mem_inter, Finset.mem_filter, Finset.mem_filter] at hw
      exact ⟨w, Finset.mem_univ _, (ex w).trans hw.1.2, (ey w).trans hw.2.2⟩
  · constructor
    · rintro ⟨e, he, h⟩
      refine ⟨e, Finset.mem_inter.2 ⟨he, Finset.mem_filter.2 ⟨Finset.mem_univ _, hM.1 e he, ?_⟩⟩⟩
      rcases h with h | h
      · left
        intro w hw
        exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (ex w).symm.trans (h w hw)⟩
      · right
        intro w hw
        exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (ey w).symm.trans (h w hw)⟩
    · rintro ⟨e, he⟩
      rw [Finset.mem_inter, Finset.mem_filter] at he
      refine ⟨e, he.1, ?_⟩
      rcases he.2.2.2 with h | h
      · left
        intro w hw
        exact (ex w).trans (Finset.mem_filter.1 (h hw)).2
      · right
        intro w hw
        exact (ey w).trans (Finset.mem_filter.1 (h hw)).2

theorem goodC_of_fan (C : Circuit) (h : FanInTwo C) : GoodC C := by
  intro g hg
  have := h g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
  exact this

theorem eval_val (C : Circuit) (n : ℕ) (l : List Bool) (h : l.length = n) :
    C.eval l = val C n C.output (fun i => l.getD i false) := by
  change C.eval l = C.eval (inp n (fun i => l.getD i false))
  rw [← list_inp l n h]

theorem classify_false (k : ℕ) (hk : 2 ≤ k) (C : Circuit) (hm : Monotone2 C) (hs : C.size + 1 ≤ 2 * k)
    (hR : ∀ u v : Fin k, C.eval (oneEach u v) = decide (u.val = v.val)) :
    ∃ M : Finset (Finset (Fin k)), IsM M ∧ ∀ x y : Fin k → Bool,
      C.eval (List.ofFn x ++ List.ofFn y) = true ↔
        Pr (fun w => w.val) (fun w => k + w.val) Finset.univ M (fun i => (List.ofFn x ++ List.ofFn y).getD i false) := by
  have hg : GoodC C := by
    intro g hg
    have := hm g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
    exact ⟨this.1.imp id Or.inl, this.2⟩
  have hmon : ∀ g ∈ C.gates, g.op ≠ GateOp.not := by
    intro g hg c
    have := (hm g hg).1
    rw [c] at this
    simp at this
  obtain ⟨M, hM, h⟩ := class_id k hk C hg hmon hs (by
    intro u v
    have := hR u v
    rw [oneEach_inp] at this
    rw [show decide (u = v) = decide (u.val = v.val) from decide_eq_decide.2 Fin.ext_iff]
    exact this)
  refine ⟨M, hM, fun x y => ?_⟩
  rw [eval_val C (k + k) _ (by simp)]
  exact h _

theorem classify_true (k : ℕ) (hk : 7 ≤ k) (C : Circuit) (hf : FanInTwo C) (hs : C.size ≤ 2 * k + 1)
    (hR : ∀ (u : Fin (k + 2)) (v : Fin (k + 1)), C.eval (oneEach u v) =
      decide (u.val ≠ k + 1 ∧ ¬ (u.val < k ∧ u.val = v.val))) :
    ∃ M : Finset (Finset (Fin k)), IsM M ∧ ∀ (x : Fin (k + 2) → Bool) (y : Fin (k + 1) → Bool),
      C.eval (List.ofFn x ++ List.ofFn y) = true ↔
        ¬ ((List.ofFn x ++ List.ofFn y).getD (k + 1) false = true ∨
          Pr (fun w => w.val) (fun w => k + 2 + w.val) Finset.univ M (fun i => (List.ofFn x ++ List.ofFn y).getD i false)) := by
  obtain ⟨M, hM, h⟩ := class_crown k hk C (goodC_of_fan C hf) hs (by
    intro u hu v hv
    have := hR ⟨u, hu⟩ ⟨v, hv⟩
    rw [oneEach_inp] at this
    change val C (k + 2 + (k + 1)) C.output (two u (k + 2 + v)) = _ at this
    rw [this, decide_eq_true_eq]
    rfl)
  refine ⟨M, hM, fun x y => ?_⟩
  rw [eval_val C (k + 2 + (k + 1)) _ (by rw [List.length_append, List.length_ofFn, List.length_ofFn])]
  exact h _

theorem construct (k nr n : ℕ) (hk : 2 ≤ k) (hn : ∀ u : Fin k, u.val < n ∧ nr + u.val < n)
    (M : Finset (Finset (Fin k))) (hM : IsM M) :
    ∃ (gs : List Gate) (o : ℕ), Mon gs ∧ gs.length + 1 = 2 * k ∧ o < n + gs.length ∧
      ∀ f, (run gs (inp n f)).getD o false = true ↔ Pr (fun w => w.val) (fun w => nr + w.val) Finset.univ M f := by
  obtain ⟨l, h1, h2⟩ := blocks nr M hM
  have hl : l ≠ [] := by
    intro c
    rw [c] at h1
    simp at h1
    omega
  have key : ∀ f, _ := fun f => build_ok nr n hn f (inp n f) (inp_len n f)
    (fun i hi => by simp [inp, List.getD_eq_getElem?_getD, hi]) l hl
  refine ⟨(build nr n l).1, (build nr n l).2, (key (fun _ => false)).2.2.2,
    (key (fun _ => false)).2.2.1.trans h1, (key (fun _ => false)).2.1, fun f => ?_⟩
  rw [(key f).1]
  exact h2 f

theorem circuit_false (k : ℕ) (hk : 2 ≤ k) (M : Finset (Finset (Fin k))) (hM : IsM M) :
    ∃ C : Circuit, Monotone2 C ∧ C.size + 1 ≤ 2 * k ∧
      (∀ u v : Fin k, C.eval (oneEach u v) = decide (u.val = v.val)) ∧
      ∀ x y : Fin k → Bool, C.eval (List.ofFn x ++ List.ofFn y) = true ↔
        Pr (fun w => w.val) (fun w => k + w.val) Finset.univ M (fun i => (List.ofFn x ++ List.ofFn y).getD i false) := by
  obtain ⟨gs, o, h1, h2, _, h4⟩ := construct k k (k + k) hk (fun u => by have := u.isLt; omega) M hM
  have ev : ∀ f, (⟨gs, o⟩ : Circuit).eval (inp (k + k) f) = true ↔
      Pr (fun w => w.val) (fun w => k + w.val) Finset.univ M f := h4
  refine ⟨⟨gs, o⟩, ?_, ?_, ?_, ?_⟩
  · intro g hg
    have := h1 g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    exact this
  · change gs.length + 1 ≤ 2 * k
    omega
  · intro u v
    have hu := u.isLt
    rw [oneEach_inp, Bool.eq_iff_iff, ev, pr_point k k u.val v.val le_rfl hu M hM, decide_eq_true_eq]
    omega
  · intro x y
    have e := list_inp (List.ofFn x ++ List.ofFn y) (k + k) (by simp)
    conv_lhs => rw [e]
    exact ev _

theorem circuit_true (k : ℕ) (hk : 2 ≤ k) (M : Finset (Finset (Fin k))) (hM : IsM M) :
    ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 2 * k + 1 ∧
      (∀ (u : Fin (k + 2)) (v : Fin (k + 1)), C.eval (oneEach u v) =
        decide (u.val ≠ k + 1 ∧ ¬ (u.val < k ∧ u.val = v.val))) ∧
      ∀ (x : Fin (k + 2) → Bool) (y : Fin (k + 1) → Bool), C.eval (List.ofFn x ++ List.ofFn y) = true ↔
        ¬ ((List.ofFn x ++ List.ofFn y).getD (k + 1) false = true ∨
          Pr (fun w => w.val) (fun w => k + 2 + w.val) Finset.univ M (fun i => (List.ofFn x ++ List.ofFn y).getD i false)) := by
  obtain ⟨gs, o, h1, h2, h3, h4⟩ := construct k (k + 2) (k + 2 + (k + 1)) hk
    (fun u => by have := u.isLt; omega) M hM
  let n := k + 2 + (k + 1)
  let m := n + gs.length
  let C : Circuit := ⟨gs ++ [⟨GateOp.or, [o, k + 1]⟩, ⟨GateOp.not, [m]⟩], m + 1⟩
  have ev : ∀ f, C.eval (inp n f) = true ↔
      ¬ (f (k + 1) = true ∨ Pr (fun w => w.val) (fun w => k + 2 + w.val) Finset.univ M f) := by
    intro f
    let w := run gs (inp n f)
    have lw : w.length = m := by simp only [w, run_length, inp_len, m]
    have a1 : w.getD (k + 1) false = f (k + 1) := by
      simp only [w]
      rw [prefix_keep _ _ (by rw [inp_len]; omega)]
      have : k + 1 < n := by omega
      simp [inp, List.getD_eq_getElem?_getD, this]
    have s1 : step w ⟨GateOp.or, [o, k + 1]⟩ = w ++ [w.getD o false || f (k + 1)] := by
      simp only [step, List.map_cons, List.map_nil, a1]
      simp [GateOp.eval]
    have s2 : ∀ b : Bool, step (w ++ [b]) ⟨GateOp.not, [m]⟩ = w ++ [b] ++ [!b] := by
      intro b
      simp only [step, List.map_cons, List.map_nil]
      rw [getD_new _ _ lw.symm]
      simp [GateOp.eval]
    have e : C.eval (inp n f) = !(w.getD o false || f (k + 1)) := by
      change (run (gs ++ [⟨GateOp.or, [o, k + 1]⟩, ⟨GateOp.not, [m]⟩]) (inp n f)).getD (m + 1) false = _
      rw [run_append]
      change (run [⟨GateOp.or, [o, k + 1]⟩, ⟨GateOp.not, [m]⟩] w).getD (m + 1) false = _
      rw [run_cons, s1, run_cons, s2, run_nil]
      exact getD_new _ _ (by simp [lw])
    rw [e, ← h4 f]
    change (!(w.getD o false || f (k + 1))) = true ↔ ¬ (f (k + 1) = true ∨ w.getD o false = true)
    cases w.getD o false <;> cases f (k + 1) <;> simp
  refine ⟨C, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    simp only [C, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with hg | rfl | rfl
    · have := h1 g hg
      exact ⟨this.1.imp id Or.inl, this.2⟩
    · simp
    · simp
  · change (gs ++ [_, _]).length ≤ 2 * k + 1
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  · intro u v
    have hu := u.isLt
    have hv := v.isLt
    rw [oneEach_inp, Bool.eq_iff_iff, ev, pr_point k (k + 2) u.val v.val (by omega) hu M hM,
      decide_eq_true_eq]
    simp only [two, decide_eq_true_eq]
    omega
  · intro x y
    have e := list_inp (List.ofFn x ++ List.ofFn y) n
      (by rw [List.length_append, List.length_ofFn, List.length_ofFn])
    conv_lhs => rw [e]
    exact ev _

end PEqualNP.Outside.L_meta_30664_aux

open PEqualNP.Outside.L_meta_30664_aux in
theorem PEqualNP.Outside.L_meta_30664 :
    ∀ (k q : Nat) (crown : Bool), 2 ≤ k → (crown = true → 7 ≤ k) →
  let nr := if crown then k+2 else k
  let nc := if crown then k+1 else k
  let A := fun (i : Fin nr) (j : Fin nc) => if crown then
    decide (i.val ≠ k+1 ∧ ¬ (i.val < k ∧ i.val = j.val)) else decide (i.val = j.val)
  let Fn := (Fin nr → Bool) → (Fin nc → Bool) → Bool
  let eligible := fun f : Fn => ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    (if crown then PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 2*k+1 else PEqualNP.MetaComplexity.Monotone2 C ∧ C.size+1 ≤ 2*k) ∧
    PEqualNP.Represents.Represents A C ∧ ∀ x y, f x y = C.eval (List.ofFn x ++ List.ofFn y)
  ∀ (X : Fin q → Fin nr → Bool) (Y : Fin q → Fin nc → Bool) (label : Fin q → Bool),
  let xs := fun (t : Fin q) => Finset.univ.filter (fun i : Fin k => (List.ofFn (X t)).getD i.val false = true)
  let ys := fun (t : Fin q) => Finset.univ.filter (fun i : Fin k => (List.ofFn (Y t)).getD i.val false = true)
  let fixed := fun t : Fin q => decide ((xs t ∩ ys t).Nonempty) ||
    (crown && (List.ofFn (X t)).getD (k+1) false)
  let target := fun t : Fin q => decide (label t = !crown)
  let D := fun t : Fin q => Finset.univ.filter (fun e : Finset (Fin k) =>
    e.card = 2 ∧ (e ⊆ xs t ∨ e ⊆ ys t))
  let valid := fun (M : Finset (Finset (Fin k))) =>
    (∀ e ∈ M, e.card = 2) ∧ (∀ e ∈ M, ∀ g ∈ M, e ≠ g → Disjoint e g)
  let err := fun (M : Finset (Finset (Fin k))) =>
    (Finset.univ.filter (fun t : Fin q =>
      (fixed t || decide ((M ∩ D t).Nonempty)) ≠ target t)).card
  let signed := fun (S : Finset (Finset (Fin k))) =>
    ((Finset.univ.filter (fun t : Fin q => fixed t = false ∧ S ⊆ D t ∧ target t = true)).card : Int) -
    ((Finset.univ.filter (fun t : Fin q => fixed t = false ∧ S ⊆ D t ∧ target t = false)).card : Int)
  let oddSets := Finset.univ.filter (fun U : Finset (Fin k) => U.card % 2 = 1)
  ∀ (I : Finset (Finset (Fin k))) (b : Nat),
    (∀ S, valid S → signed S ≠ 0 → (S \ I).card ≤ 1) →
    ((∀ f : Fn, eligible f → b ≤ (Finset.univ.filter (fun t : Fin q => f (X t) (Y t) ≠ label t)).card) ↔
      ∀ K ⊆ I, valid K → ∃ (y : Fin k → Rat) (z : Finset (Fin k) → Rat),
        (∀ v, 0 ≤ y v) ∧ (∀ U, 0 ≤ z U) ∧
        (oddSets.filter (fun U => z U ≠ 0)).card ≤ k*(k-1)/2 ∧
        (∀ e : Finset (Fin k), e.card = 2 → e ∉ I → (∀ g ∈ K, Disjoint e g) →
          (err K : Rat) - (err (insert e K) : Rat) ≤
            (∑ v ∈ e, y v) + ∑ U ∈ oddSets.filter (fun T => e ⊆ T), z U) ∧
        (∑ v : Fin k, y v) + (∑ U ∈ oddSets, ((U.card/2 : Nat) : Rat)*z U) ≤
          (err K : Rat) - (b : Rat)) := by
  intro k q crown hk h7
  cases crown
  · intro nr nc A Fn eligible X Y label xs ys fixed target D valid err signed oddSets I b hsig
    refine Iff.trans ?_ (comb fixed target D I b hsig)
    let X' : Fin q → Fin k → Bool := X
    let Y' : Fin q → Fin k → Bool := Y
    have errs : ∀ (M : Finset (Finset (Fin k))), IsM M → ∀ f : (Fin k → Bool) → (Fin k → Bool) → Bool,
        (∀ x y : Fin k → Bool, f x y = true ↔ Pr (fun w => w.val) (fun w => k + w.val) Finset.univ M
          (fun i => (List.ofFn x ++ List.ofFn y).getD i false)) →
        (Finset.univ.filter (fun t : Fin q => f (X' t) (Y' t) ≠ label t)).card = errF fixed target D M := by
      intro M hM f hf
      unfold errF
      congr 1
      apply Finset.filter_congr
      intro t _
      have e1 : f (X' t) (Y' t) = (fixed t || decide ((M ∩ D t).Nonempty)) := by
        rw [Bool.eq_iff_iff, hf, pr_pred k k k le_rfl le_rfl _ _ M hM]
        have e2 : fixed t = decide ((xs t ∩ ys t).Nonempty) := by
          change (decide ((xs t ∩ ys t).Nonempty) || (false && _)) = _
          rw [Bool.false_and, Bool.or_false]
        rw [e2, Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq]
      have e3 : target t = label t := by
        change decide (label t = !false) = label t
        cases label t <;> rfl
      rw [e1, e3]
    constructor
    · intro h M hM
      obtain ⟨C, hm, hs, hR, hv⟩ := circuit_false k hk M hM
      let f : (Fin k → Bool) → (Fin k → Bool) → Bool := fun x y => C.eval (List.ofFn x ++ List.ofFn y)
      have hel : eligible f := ⟨C, ⟨hm, hs⟩, hR, fun _ _ => rfl⟩
      exact (h f hel).trans (le_of_eq (errs M hM f hv))
    · intro h f hf
      obtain ⟨C, hC, hR, hv⟩ := hf
      have hC' : PEqualNP.MetaComplexity.Monotone2 C ∧ C.size + 1 ≤ 2 * k := hC
      have hR' : ∀ u v : Fin k, C.eval (PEqualNP.Represents.oneEach u v) = decide (u.val = v.val) := hR
      have hv' : ∀ x y : Fin k → Bool, (show (Fin k → Bool) → (Fin k → Bool) → Bool from f) x y =
          C.eval (List.ofFn x ++ List.ofFn y) := hv
      obtain ⟨M, hM, hc⟩ := classify_false k hk C hC'.1 hC'.2 hR'
      refine (h M hM).trans (le_of_eq (errs M hM f (fun x y => ?_)).symm)
      rw [hv' x y]
      exact hc x y
  · intro nr nc A Fn eligible X Y label xs ys fixed target D valid err signed oddSets I b hsig
    refine Iff.trans ?_ (comb fixed target D I b hsig)
    let X' : Fin q → Fin (k + 2) → Bool := X
    let Y' : Fin q → Fin (k + 1) → Bool := Y
    have errs : ∀ (M : Finset (Finset (Fin k))), IsM M →
        ∀ f : (Fin (k + 2) → Bool) → (Fin (k + 1) → Bool) → Bool,
        (∀ (x : Fin (k + 2) → Bool) (y : Fin (k + 1) → Bool), f x y = true ↔
          ¬ ((List.ofFn x ++ List.ofFn y).getD (k + 1) false = true ∨
            Pr (fun w => w.val) (fun w => k + 2 + w.val) Finset.univ M
              (fun i => (List.ofFn x ++ List.ofFn y).getD i false))) →
        (Finset.univ.filter (fun t : Fin q => f (X' t) (Y' t) ≠ label t)).card = errF fixed target D M := by
      intro M hM f hf
      unfold errF
      congr 1
      apply Finset.filter_congr
      intro t _
      have e1 : f (X' t) (Y' t) = !(fixed t || decide ((M ∩ D t).Nonempty)) := by
        have e2 : fixed t = (decide ((xs t ∩ ys t).Nonempty) || (List.ofFn (X' t)).getD (k + 1) false) := by
          change (decide ((xs t ∩ ys t).Nonempty) || (true && (List.ofFn (X' t)).getD (k + 1) false)) = _
          rw [Bool.true_and]
        have e4 : (List.ofFn (X' t) ++ List.ofFn (Y' t)).getD (k + 1) false =
            (List.ofFn (X' t)).getD (k + 1) false := getD_keep _ _ (by simp)
        rw [Bool.eq_iff_iff, hf, pr_pred k (k + 2) (k + 1) (by omega) (by omega) _ _ M hM, e4,
          Bool.not_eq_true', ← Bool.not_eq_true, e2, Bool.or_eq_true, Bool.or_eq_true,
          decide_eq_true_eq, decide_eq_true_eq]
        apply not_congr
        exact or_left_comm.trans or_assoc.symm
      have e3 : target t = !label t := by
        change decide (label t = !true) = !label t
        cases label t <;> rfl
      rw [e1, e3]
      cases (fixed t || decide ((M ∩ D t).Nonempty)) <;> cases label t <;> simp
    constructor
    · intro h M hM
      obtain ⟨C, hm, hs, hR, hv⟩ := circuit_true k hk M hM
      let f : (Fin (k + 2) → Bool) → (Fin (k + 1) → Bool) → Bool :=
        fun x y => C.eval (List.ofFn x ++ List.ofFn y)
      have hel : eligible f := ⟨C, ⟨hm, hs⟩, hR, fun _ _ => rfl⟩
      exact (h f hel).trans (le_of_eq (errs M hM f hv))
    · intro h f hf
      obtain ⟨C, hC, hR, hv⟩ := hf
      have hC' : PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 2 * k + 1 := hC
      have hR' : ∀ (u : Fin (k + 2)) (v : Fin (k + 1)), C.eval (PEqualNP.Represents.oneEach u v) =
          decide (u.val ≠ k + 1 ∧ ¬ (u.val < k ∧ u.val = v.val)) := hR
      have hv' : ∀ (x : Fin (k + 2) → Bool) (y : Fin (k + 1) → Bool),
          (show (Fin (k + 2) → Bool) → (Fin (k + 1) → Bool) → Bool from f) x y =
            C.eval (List.ofFn x ++ List.ofFn y) := hv
      obtain ⟨M, hM, hc⟩ := classify_true k (h7 rfl) C hC'.1 hC'.2 hR'
      refine (h M hM).trans (le_of_eq (errs M hM f (fun x y => ?_)).symm)
      rw [hv' x y]
      exact hc x y
